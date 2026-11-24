// mend: applies AI-written edits in four formats to a tree of text files.
// My own implementation of SPEC.md (version 1). Node 22, standard library only.
// Formats: unified diff, SEARCH/REPLACE blocks, V4A patches, JSON tool calls.
// Matching at three tiers (exact, trim trailing, trim both), all-or-nothing writes.

import { mkdirSync, readFileSync, rmSync, statSync, writeFileSync, writeSync } from 'node:fs';
import { dirname } from 'node:path';

const FORMATS = ['auto', 'unified', 'search-replace', 'v4a', 'json'];

class ParseErr {
  readonly line: string;
  constructor(line: string) {
    this.line = line;
  }
}

class EditFail {
  readonly code: string;
  readonly path: string;
  constructor(code: string, path: string) {
    this.code = code;
    this.path = path;
  }
}

const isBlank = (s: string): boolean => s.trim() === '';
const trimEnd = (s: string): string => s.replace(/[ \t]+$/, '');
const trimBoth = (s: string): string => s.replace(/^[ \t]+/, '').replace(/[ \t]+$/, '');
const leadWs = (s: string): string => (/^[ \t]*/.exec(s) ?? [''])[0]!;

function patchLines(text: string): string[] {
  if (text === '') return [];
  const lines = text.split('\n');
  if (text.endsWith('\n')) lines.pop();
  return lines.map((l) => (l.endsWith('\r') ? l.slice(0, -1) : l));
}

function isSafePath(p: string): boolean {
  if (p === '' || p.startsWith('/') || p.includes('\\')) return false;
  return p.split('/').every((s) => s !== '' && s !== '.' && s !== '..');
}

interface FileState {
  lines: string[];
  br: '\n' | '\r\n';
  eol: boolean;
}

function parseFile(text: string): FileState {
  let br: '\n' | '\r\n' = '\n';
  const nl = text.indexOf('\n');
  if (nl > 0 && text[nl - 1] === '\r') br = '\r\n';
  if (text === '') return { lines: [], br, eol: false };
  const parts = text.split(br);
  const eol = parts[parts.length - 1] === '';
  if (eol) parts.pop();
  return { lines: parts, br, eol };
}

function renderFile(st: FileState): string {
  if (st.lines.length === 0) return '';
  return st.lines.join(st.br) + (st.eol ? st.br : '');
}

/** The tree as the edits leave it: changed paths in `now` (null: deleted). */
class Tree {
  private readonly orig = new Map<string, string | null>();
  readonly now = new Map<string, string | null>();
  readonly moves: Array<[string, string]> = [];

  original(p: string): string | null {
    if (!this.orig.has(p)) {
      let v: string | null = null;
      try {
        if (statSync(p).isFile()) v = readFileSync(p, 'utf8');
      } catch {
        v = null;
      }
      this.orig.set(p, v);
    }
    return this.orig.get(p)!;
  }

  get(p: string): string | null {
    return this.now.has(p) ? this.now.get(p)! : this.original(p);
  }

  state(p: string): FileState | null {
    const t = this.get(p);
    return t === null ? null : parseFile(t);
  }
}

type Edit = (tree: Tree) => void;

function keyAt(line: string, tier: number): string {
  if (tier === 0) return line;
  if (tier === 1) return trimEnd(line);
  return trimBoth(line);
}

function occurrences(lines: string[], o: string[], tier: number, from: number): number[] {
  const out: number[] = [];
  if (o.length === 0) return out;
  for (let i = from; i + o.length <= lines.length; i++) {
    let ok = true;
    for (let j = 0; j < o.length; j++) {
      if (keyAt(lines[i + j]!, tier) !== keyAt(o[j]!, tier)) {
        ok = false;
        break;
      }
    }
    if (ok) out.push(i);
  }
  return out;
}

function findTier(lines: string[], o: string[], strict: boolean, from: number): { tier: number; pos: number[] } | null {
  const tiers = strict ? [0] : [0, 1, 2];
  for (const t of tiers) {
    const pos = occurrences(lines, o, t, from);
    if (pos.length > 0) return { tier: t, pos };
  }
  return null;
}

function reindent(line: string, f: string, p: string): string {
  if (line.trim() === '') return line;
  if (line.startsWith(p)) return f + line.slice(p.length);
  return line;
}

interface BodyItem {
  kind: 'ctx' | 'old' | 'new' | 'bs';
  text: string;
}

interface HunkData {
  o: string[];
  n: string[];
  nCtx: number[];
}

function hunkData(body: BodyItem[]): HunkData {
  const o: string[] = [];
  const n: string[] = [];
  const nCtx: number[] = [];
  for (const b of body) {
    if (b.kind === 'ctx') {
      nCtx.push(o.length);
      o.push(b.text);
      n.push(b.text);
    } else if (b.kind === 'old') {
      o.push(b.text);
    } else if (b.kind === 'new') {
      nCtx.push(-1);
      n.push(b.text);
    }
  }
  return { o, n, nCtx };
}

function applyReplace(lines: string[], pos: number, d: HunkData, tier: number): string[] {
  const f = leadWs(lines[pos]!);
  const p = leadWs(d.o[0]!);
  const mapped = d.n.map((text, i) => {
    const oi = d.nCtx[i]!;
    if (oi >= 0) return lines[pos + oi]!;
    if (tier === 2) return reindent(text, f, p);
    return text;
  });
  return [...lines.slice(0, pos), ...mapped, ...lines.slice(pos + d.o.length)];
}

/** True when a `\` line follows the hunk body's last context or `+` line. */
function trailingBs(body: BodyItem[]): boolean {
  let last = -1;
  for (let i = 0; i < body.length; i++) {
    if (body[i]!.kind === 'ctx' || body[i]!.kind === 'new') last = i;
  }
  return last >= 0 && last + 1 < body.length && body[last + 1]!.kind === 'bs';
}

function detectFormat(lines: string[]): string | null {
  const first = lines.findIndex((l) => !isBlank(l));
  if (first < 0) return null;
  if (lines[first]!.trim() === '*** Begin Patch') return 'v4a';
  const c = lines[first]!.trimStart()[0];
  if (c === '[' || c === '{') return 'json';
  if (lines.some((l) => trimEnd(l) === '<<<<<<< SEARCH')) return 'search-replace';
  if (lines.some((l, i) => l.startsWith('diff --git ') || (l.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')))) return 'unified';
  return null;
}

// ---- JSON edits (SPEC section 9) ----

function jsonEdit(v: unknown): Edit | null {
  if (v === null || typeof v !== 'object' || Array.isArray(v)) return null;
  const o = v as Record<string, unknown>;
  const p = o.path;
  if (typeof p !== 'string') return null;
  if (o.command === 'create') {
    if (typeof o.file_text !== 'string') return null;
    const text = o.file_text;
    return (tree) => {
      if (!isSafePath(p)) throw new EditFail('unsafe', p);
      if (tree.get(p) !== null) throw new EditFail('exists', p);
      tree.now.set(p, text);
    };
  }
  if (o.command === 'str_replace') {
    if (typeof o.old_str !== 'string' || o.old_str === '') return null;
    if (o.new_str !== undefined && typeof o.new_str !== 'string') return null;
    const oldStr = o.old_str;
    const newStr = (o.new_str as string | undefined) ?? '';
    return (tree) => {
      if (!isSafePath(p)) throw new EditFail('unsafe', p);
      const before = tree.get(p);
      if (before === null) throw new EditFail('missing', p);
      const nl = before.indexOf('\n');
      const crlf = nl > 0 && before[nl - 1] === '\r';
      const toLf = (s: string): string => (crlf ? s.replaceAll('\r\n', '\n') : s);
      const t = toLf(before);
      const old = toLf(oldStr);
      let count = 0;
      for (let k = t.indexOf(old); k >= 0; k = t.indexOf(old, k + 1)) count++;
      if (count === 0) throw new EditFail('no-match', p);
      if (count > 1) throw new EditFail('ambiguous', p);
      const at = t.indexOf(old);
      const out = t.slice(0, at) + toLf(newStr) + t.slice(at + old.length);
      tree.now.set(p, crlf ? out.replaceAll('\n', '\r\n') : out);
    };
  }
  if (o.command === 'insert') {
    if (typeof o.insert_line !== 'number' || !Number.isInteger(o.insert_line)) return null;
    if (typeof o.new_str !== 'string') return null;
    const line = o.insert_line;
    const add = patchLines(o.new_str);
    return (tree) => {
      if (!isSafePath(p)) throw new EditFail('unsafe', p);
      const before = tree.get(p);
      if (before === null) throw new EditFail('missing', p);
      const st = parseFile(before);
      if (line < 0 || line > st.lines.length) throw new EditFail('no-match', p);
      const lines = [...st.lines];
      lines.splice(line, 0, ...add);
      tree.now.set(p, renderFile({ lines, br: st.br, eol: st.eol }));
    };
  }
  return null;
}

function jsonEdits(text: string, lines: string[]): Edit[] {
  const first = lines.findIndex((l) => !isBlank(l));
  if (first < 0) throw new ParseErr('error: parse 1');
  const edits: Edit[] = [];
  if (lines[first]!.trimStart().startsWith('[')) {
    let v: unknown;
    try {
      v = JSON.parse(text);
    } catch {
      throw new ParseErr(`error: parse ${first + 1}`);
    }
    if (!Array.isArray(v)) throw new ParseErr(`error: parse ${first + 1}`);
    for (const x of v) {
      const e = jsonEdit(x);
      if (e === null) throw new ParseErr(`error: parse ${first + 1}`);
      edits.push(e);
    }
    return edits;
  }
  lines.forEach((l, i) => {
    if (isBlank(l)) return;
    let e: Edit | null = null;
    try {
      e = jsonEdit(JSON.parse(l));
    } catch {
      e = null;
    }
    if (e === null) throw new ParseErr(`error: parse ${i + 1}`);
    edits.push(e);
  });
  return edits;
}

// ---- unified diffs (SPEC section 6) ----

interface UniHunk {
  a: number;
  body: BodyItem[];
}

interface UniSection {
  pairOld: string | null | undefined;
  pairNew: string | null | undefined;
  renameFrom: string | undefined;
  renameTo: string | undefined;
  diffOld: string | undefined;
  diffNew: string | undefined;
  newFile: boolean;
  delFile: boolean;
  hunks: UniHunk[];
}

function headerPath(line: string): string | null {
  let p = line.slice(4);
  const tab = p.indexOf('\t');
  if (tab >= 0) p = p.slice(0, tab);
  p = p.trim();
  if (p === '/dev/null') return null;
  if (p.startsWith('a/') || p.startsWith('b/')) p = p.slice(2);
  return p;
}

const HUNK_RE = /^@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@(.*)$/;
const DIFF_RE = /^diff --git a\/(\S+) b\/(\S+)$/;

function parseUnified(lines: string[], strict: boolean): Edit[] {
  const sections: UniSection[] = [];
  let i = 0;
  while (i < lines.length) {
    const line = lines[i]!;
    if (line.startsWith('diff --git ')) {
      const dm = DIFF_RE.exec(line);
      if (!dm) throw new ParseErr(`error: parse ${i + 1}`);
      const s: UniSection = {
        pairOld: undefined, pairNew: undefined, renameFrom: undefined, renameTo: undefined,
        diffOld: dm[1], diffNew: dm[2], newFile: false, delFile: false, hunks: [],
      };
      sections.push(s);
      i++;
      i = parseUniSection(lines, i, s);
    } else if (line.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')) {
      const s: UniSection = {
        pairOld: undefined, pairNew: undefined, renameFrom: undefined, renameTo: undefined,
        diffOld: undefined, diffNew: undefined, newFile: false, delFile: false, hunks: [],
      };
      sections.push(s);
      i = parseUniSection(lines, i, s);
    } else if (line.startsWith('@@')) {
      throw new ParseErr(`error: parse ${i + 1}`);
    } else {
      i++;
    }
  }
  return sections.map((s) => uniEdit(s, strict));
}

function parseUniSection(lines: string[], start: number, s: UniSection): number {
  let i = start;
  let inHeader = true;
  while (i < lines.length) {
    const line = lines[i]!;
    if (line.startsWith('diff --git ')) return i;
    if (line.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')) {
      if (inHeader && s.pairOld === undefined) {
        s.pairOld = headerPath(line);
        s.pairNew = headerPath(lines[i + 1]!);
        i += 2;
        continue;
      }
      return i;
    }
    if (line.startsWith('--- ')) {
      if (inHeader) throw new ParseErr(`error: parse ${i + 2}`);
      i++;
      continue;
    }
    if (line.startsWith('+++ ')) {
      if (inHeader && s.pairNew === undefined) s.pairNew = headerPath(line);
      i++;
      continue;
    }
    if (line.startsWith('@@')) {
      const m = HUNK_RE.exec(line);
      if (!m) throw new ParseErr(`error: parse ${i + 1}`);
      inHeader = false;
      const a = parseInt(m[1]!, 10);
      i++;
      const body: BodyItem[] = [];
      while (i < lines.length) {
        const bl = lines[i]!;
        if (bl.startsWith('diff --git ')) break;
        if (bl.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')) break;
        if (bl.startsWith('@@')) break;
        if (bl === '') body.push({ kind: 'ctx', text: '' });
        else if (bl.startsWith(' ')) body.push({ kind: 'ctx', text: bl.slice(1) });
        else if (bl.startsWith('-')) body.push({ kind: 'old', text: bl.slice(1) });
        else if (bl.startsWith('+')) body.push({ kind: 'new', text: bl.slice(1) });
        else if (bl.startsWith('\\')) body.push({ kind: 'bs', text: bl.slice(1) });
        else break;
        i++;
      }
      while (body.length > 0 && body[body.length - 1]!.kind === 'ctx' && body[body.length - 1]!.text === '') body.pop();
      s.hunks.push({ a, body });
      continue;
    }
    if (inHeader) {
      if (line.startsWith('rename from ')) s.renameFrom = line.slice('rename from '.length);
      else if (line.startsWith('rename to ')) s.renameTo = line.slice('rename to '.length);
      else if (line === 'new file mode' || line.startsWith('new file mode ')) s.newFile = true;
      else if (line === 'deleted file mode' || line.startsWith('deleted file mode ')) s.delFile = true;
      i++;
      continue;
    }
    i++;
  }
  return i;
}

function applyUniHunks(st: FileState, hunks: UniHunk[], strict: boolean, path: string): FileState {
  let lines = [...st.lines];
  let eol = st.eol;
  let d = 0;
  for (const h of hunks) {
    const data = hunkData(h.body);
    const tBs = trailingBs(h.body);
    if (data.o.length === 0) {
      const idx = Math.max(0, Math.min(h.a + d, lines.length));
      const atEnd = idx === lines.length;
      lines.splice(idx, 0, ...data.n);
      if (atEnd) eol = !tBs;
      d += data.n.length;
    } else {
      const found = findTier(lines, data.o, strict, 0);
      if (!found) throw new EditFail('no-match', path);
      const target = h.a - 1 + d;
      let best = found.pos[0]!;
      for (const p of found.pos) {
        if (Math.abs(p - target) < Math.abs(best - target)) best = p;
      }
      const atEnd = best + data.o.length === lines.length;
      lines = applyReplace(lines, best, data, found.tier);
      if (atEnd) eol = !tBs;
      d += data.n.length - data.o.length;
    }
  }
  return { lines, br: st.br, eol };
}

function uniEdit(s: UniSection, strict: boolean): Edit {
  const old = s.pairOld !== undefined ? s.pairOld : (s.renameFrom !== undefined ? s.renameFrom : s.diffOld);
  const nw = s.pairNew !== undefined ? s.pairNew : (s.renameTo !== undefined ? s.renameTo : s.diffNew);
  return (tree) => {
    if (old === null || s.newFile) {
      const np = nw;
      if (np === null || np === undefined) return;
      if (!isSafePath(np)) throw new EditFail('unsafe', np);
      if (tree.get(np) !== null) throw new EditFail('exists', np);
      const plus: string[] = [];
      let lastBs = false;
      for (const h of s.hunks) {
        for (let j = 0; j < h.body.length; j++) {
          const b = h.body[j]!;
          if (b.kind === 'new') {
            plus.push(b.text);
            lastBs = j + 1 < h.body.length && h.body[j + 1]!.kind === 'bs';
          }
        }
      }
      tree.now.set(np, plus.length === 0 ? '' : plus.join('\n') + (lastBs ? '' : '\n'));
      return;
    }
    if (nw === null || s.delFile) {
      const op = old;
      if (op === null || op === undefined) return;
      if (!isSafePath(op)) throw new EditFail('unsafe', op);
      if (tree.get(op) === null) throw new EditFail('missing', op);
      tree.now.set(op, null);
      return;
    }
    const op = old!;
    const np = nw!;
    if (!isSafePath(op)) throw new EditFail('unsafe', op);
    if (!isSafePath(np)) throw new EditFail('unsafe', np);
    const cur = tree.state(op);
    if (cur === null) throw new EditFail('missing', op);
    if (op !== np && tree.get(np) !== null) throw new EditFail('exists', np);
    const next = applyUniHunks(cur, s.hunks, strict, op);
    if (op !== np) {
      tree.now.set(np, renderFile(next));
      tree.now.set(op, null);
      tree.moves.push([op, np]);
    } else {
      tree.now.set(op, renderFile(next));
    }
  };
}

// ---- SEARCH/REPLACE blocks (SPEC section 7) ----

interface SrBlock {
  path: string;
  old: string[];
  new: string[];
}

function parseSearchReplace(lines: string[], strict: boolean): Edit[] {
  const blocks: SrBlock[] = [];
  let i = 0;
  let prevEnd = -1;
  let prevPath: string | null = null;
  while (i < lines.length) {
    if (trimEnd(lines[i]!) !== '<<<<<<< SEARCH') {
      i++;
      continue;
    }
    const s = i;
    let path: string | null = null;
    for (let j = s - 1; j > prevEnd; j--) {
      const l = lines[j]!;
      if (isBlank(l)) continue;
      if (l.trim().startsWith('```')) continue;
      path = l.trim();
      break;
    }
    if (path === null) {
      if (prevPath !== null) path = prevPath;
      else throw new ParseErr(`error: parse ${s + 1}`);
    }
    let eq = -1;
    for (let j = s + 1; j < lines.length; j++) {
      if (trimEnd(lines[j]!) === '=======') {
        eq = j;
        break;
      }
    }
    if (eq < 0) throw new ParseErr(`error: parse ${s + 1}`);
    let rep = -1;
    for (let j = eq + 1; j < lines.length; j++) {
      if (trimEnd(lines[j]!) === '>>>>>>> REPLACE') {
        rep = j;
        break;
      }
    }
    if (rep < 0) throw new ParseErr(`error: parse ${s + 1}`);
    blocks.push({ path, old: lines.slice(s + 1, eq), new: lines.slice(eq + 1, rep) });
    prevEnd = rep;
    prevPath = path;
    i = rep + 1;
  }
  return blocks.map((b) => srEdit(b, strict));
}

function srEdit(b: SrBlock, strict: boolean): Edit {
  return (tree) => {
    if (!isSafePath(b.path)) throw new EditFail('unsafe', b.path);
    if (b.old.length === 0) {
      if (tree.get(b.path) !== null) throw new EditFail('exists', b.path);
      tree.now.set(b.path, b.new.length === 0 ? '' : b.new.join('\n') + '\n');
      return;
    }
    const cur = tree.state(b.path);
    if (cur === null) throw new EditFail('missing', b.path);
    const found = findTier(cur.lines, b.old, strict, 0);
    if (!found) throw new EditFail('no-match', b.path);
    if (found.pos.length > 1) throw new EditFail('ambiguous', b.path);
    const data: HunkData = { o: b.old, n: b.new, nCtx: b.new.map(() => -1) };
    const next = applyReplace(cur.lines, found.pos[0]!, data, found.tier);
    tree.now.set(b.path, renderFile({ lines: next, br: cur.br, eol: cur.eol }));
  };
}

// ---- V4A patches (SPEC section 8) ----

interface VChunk {
  anchor: string | null;
  body: BodyItem[];
  eof: boolean;
}

interface VSection {
  kind: 'add' | 'delete' | 'update';
  path: string;
  lines?: string[];
  moveTo?: string | null;
  chunks?: VChunk[];
  lineNo: number;
}

function parseV4a(lines: string[], strict: boolean): Edit[] {
  const first = lines.findIndex((l) => !isBlank(l));
  if (first < 0) throw new ParseErr('error: parse 1');
  if (lines[first]!.trim() !== '*** Begin Patch') throw new ParseErr(`error: parse ${first + 1}`);
  let last = -1;
  for (let i = lines.length - 1; i >= 0; i--) {
    if (!isBlank(lines[i]!)) {
      last = i;
      break;
    }
  }
  if (last < 0 || lines[last]!.trim() !== '*** End Patch') throw new ParseErr(`error: parse ${lines.length + 1}`);
  const sections: VSection[] = [];
  let i = first + 1;
  const sectionKind = (l: string): 'add' | 'delete' | 'update' | null => {
    if (l.startsWith('*** Add File:')) return 'add';
    if (l.startsWith('*** Delete File:')) return 'delete';
    if (l.startsWith('*** Update File:')) return 'update';
    return null;
  };
  while (i < last) {
    const line = lines[i]!;
    if (isBlank(line)) {
      i++;
      continue;
    }
    const kind = sectionKind(line);
    if (kind === null) throw new ParseErr(`error: parse ${i + 1}`);
    const path = line.slice(line.indexOf(':') + 1).trim();
    const lineNo = i + 1;
    i++;
    if (kind === 'add') {
      const rawStart = i;
      const raw: string[] = [];
      while (i < last) {
        const l = lines[i]!;
        if (sectionKind(l) !== null) break;
        raw.push(l);
        i++;
      }
      while (raw.length > 0 && isBlank(raw[raw.length - 1]!)) raw.pop();
      const content: string[] = [];
      raw.forEach((l, k) => {
        if (l === '') content.push('');
        else if (l.startsWith('+')) content.push(l.slice(1));
        else throw new ParseErr(`error: parse ${rawStart + k + 1}`);
      });
      sections.push({ kind: 'add', path, lines: content, lineNo });
    } else if (kind === 'delete') {
      while (i < last) {
        const l = lines[i]!;
        if (sectionKind(l) !== null) break;
        if (isBlank(l)) {
          i++;
          continue;
        }
        throw new ParseErr(`error: parse ${i + 1}`);
      }
      sections.push({ kind: 'delete', path, lineNo });
    } else {
      while (i < last && isBlank(lines[i]!)) i++;
      let moveTo: string | null = null;
      if (i < last && lines[i]!.startsWith('*** Move to:')) {
        moveTo = lines[i]!.slice('*** Move to:'.length).trim();
        i++;
      }
      const chunks: VChunk[] = [];
      let cur: VChunk | null = null;
      let seenChunk = false;
      const flush = (): void => {
        if (cur !== null) {
          chunks.push(cur);
          cur = null;
        }
      };
      while (i < last) {
        const l = lines[i]!;
        if (sectionKind(l) !== null) break;
        if (l.trim() === '*** End of File') {
          if (cur === null) throw new ParseErr(`error: parse ${i + 1}`);
          cur.eof = true;
          flush();
          i++;
          continue;
        }
        if (l.startsWith('@@')) {
          flush();
          seenChunk = true;
          cur = { anchor: l.slice(2).trim(), body: [], eof: false };
          i++;
          continue;
        }
        if (l === '') {
          if (!seenChunk) {
            seenChunk = true;
            cur = { anchor: null, body: [], eof: false };
          }
          if (cur !== null) cur.body.push({ kind: 'ctx', text: '' });
          i++;
          continue;
        }
        if (l.startsWith(' ')) {
          if (cur === null) {
            seenChunk = true;
            cur = { anchor: null, body: [], eof: false };
          }
          cur.body.push({ kind: 'ctx', text: l.slice(1) });
          i++;
          continue;
        }
        if (l.startsWith('-')) {
          if (cur === null) {
            seenChunk = true;
            cur = { anchor: null, body: [], eof: false };
          }
          cur.body.push({ kind: 'old', text: l.slice(1) });
          i++;
          continue;
        }
        if (l.startsWith('+')) {
          if (cur === null) {
            seenChunk = true;
            cur = { anchor: null, body: [], eof: false };
          }
          cur.body.push({ kind: 'new', text: l.slice(1) });
          i++;
          continue;
        }
        if (isBlank(l)) {
          if (cur !== null) throw new ParseErr(`error: parse ${i + 1}`);
          i++;
          continue;
        }
        throw new ParseErr(`error: parse ${i + 1}`);
      }
      flush();
      if (chunks.length > 0) {
        const lc = chunks[chunks.length - 1]!;
        if (!lc.eof) {
          while (lc.body.length > 0) {
            const b = lc.body[lc.body.length - 1]!;
            if (b.kind === 'ctx' && b.text.trim() === '') lc.body.pop();
            else break;
          }
        }
      }
      if (chunks.length === 0 && moveTo === null) throw new ParseErr(`error: parse ${lineNo}`);
      sections.push({ kind: 'update', path, moveTo, chunks, lineNo });
    }
  }
  return sections.map((s) => vEdit(s, strict));
}

function findAnchor(lines: string[], anchor: string, cursor: number, strict: boolean): number | null {
  const tiers = strict ? [0] : [0, 1, 2];
  for (const t of tiers) {
    for (let i = cursor; i < lines.length; i++) {
      if (keyAt(lines[i]!, t) === keyAt(anchor, t)) return i;
    }
  }
  return null;
}

function applyV4aChunks(st: FileState, chunks: VChunk[], strict: boolean, path: string): FileState {
  let lines = [...st.lines];
  let cursor = 0;
  for (const ch of chunks) {
    if (ch.anchor !== null && ch.anchor !== '') {
      const aIdx = findAnchor(lines, ch.anchor, cursor, strict);
      if (aIdx === null) throw new EditFail('no-match', path);
      cursor = aIdx + 1;
    }
    const data = hunkData(ch.body);
    if (data.o.length === 0) {
      const idx = ch.eof ? lines.length : cursor;
      lines.splice(idx, 0, ...data.n);
      cursor = idx + data.n.length;
    } else {
      const found = findTier(lines, data.o, strict, cursor);
      if (!found) throw new EditFail('no-match', path);
      let positions = found.pos;
      if (ch.eof) {
        positions = positions.filter((p) => p + data.o.length === lines.length);
        if (positions.length === 0) throw new EditFail('no-match', path);
      }
      const pos = positions[0]!;
      lines = applyReplace(lines, pos, data, found.tier);
      cursor = pos + data.n.length;
    }
  }
  return { lines, br: st.br, eol: st.eol };
}

function vEdit(s: VSection, strict: boolean): Edit {
  return (tree) => {
    if (s.kind === 'add') {
      if (!isSafePath(s.path)) throw new EditFail('unsafe', s.path);
      if (tree.get(s.path) !== null) throw new EditFail('exists', s.path);
      const content = s.lines ?? [];
      tree.now.set(s.path, content.length === 0 ? '' : content.join('\n') + '\n');
      return;
    }
    if (s.kind === 'delete') {
      if (!isSafePath(s.path)) throw new EditFail('unsafe', s.path);
      if (tree.get(s.path) === null) throw new EditFail('missing', s.path);
      tree.now.set(s.path, null);
      return;
    }
    if (!isSafePath(s.path)) throw new EditFail('unsafe', s.path);
    if (s.moveTo !== null && s.moveTo !== undefined && !isSafePath(s.moveTo)) throw new EditFail('unsafe', s.moveTo);
    const cur = tree.state(s.path);
    if (cur === null) throw new EditFail('missing', s.path);
    if (s.moveTo && tree.get(s.moveTo) !== null) throw new EditFail('exists', s.moveTo);
    const next = applyV4aChunks(cur, s.chunks ?? [], strict, s.path);
    if (s.moveTo) {
      tree.now.set(s.moveTo, renderFile(next));
      tree.now.set(s.path, null);
      tree.moves.push([s.path, s.moveTo]);
    } else {
      tree.now.set(s.path, renderFile(next));
    }
  };
}

// ---- main: invocation, output, atomicity (SPEC sections 1, 2, 10) ----

function run(args: string[]): { code: number; out: string[] } {
  let format: string | null = null;
  let check = false;
  let strict = false;
  const pos: string[] = [];
  let ended = false;
  for (const a of args) {
    if (!ended && a === '--') {
      ended = true;
    } else if (!ended && a.startsWith('-') && a !== '-') {
      if (a.startsWith('--format=') && format === null && FORMATS.includes(a.slice(9))) format = a.slice(9);
      else if (a === '--check' && !check) check = true;
      else if (a === '--strict' && !strict) strict = true;
      else return { code: 2, out: ['error: usage'] };
    } else {
      pos.push(a);
    }
  }
  if (pos.length > 1) return { code: 2, out: ['error: usage'] };
  const file = pos.length === 0 || pos[0] === '-' ? null : pos[0]!;
  let text = '';
  try {
    text = readFileSync(file ?? 0, 'utf8');
  } catch {
    if (file !== null) return { code: 2, out: ['error: no-patch'] };
  }
  const lines = patchLines(text);
  const kind = format === null || format === 'auto' ? detectFormat(lines) : format;
  if (kind === null) return { code: 2, out: ['error: format'] };
  let edits: Edit[];
  try {
    if (kind === 'json') edits = jsonEdits(text, lines);
    else if (kind === 'unified') edits = parseUnified(lines, strict);
    else if (kind === 'search-replace') edits = parseSearchReplace(lines, strict);
    else edits = parseV4a(lines, strict);
    if (edits.length === 0) throw new ParseErr('error: parse 1');
  } catch (e) {
    if (e instanceof ParseErr) return { code: 2, out: [e.line] };
    throw e;
  }
  const tree = new Tree();
  const fails: EditFail[] = [];
  for (const edit of edits) {
    const before = new Map(tree.now);
    const movesBefore = tree.moves.length;
    try {
      edit(tree);
    } catch (e) {
      if (!(e instanceof EditFail)) throw e;
      tree.now.clear();
      for (const [k, v] of before) tree.now.set(k, v);
      tree.moves.length = movesBefore;
      fails.push(e);
    }
  }
  if (fails.length > 0) {
    return {
      code: 1,
      out: [...fails.map((f) => `error: ${f.code} ${f.path}`), `failed: ${fails.length} of ${edits.length} edits`],
    };
  }
  const rows: Array<{ key: string; line: string }> = [];
  const rOld = new Set<string>();
  const rNew = new Set<string>();
  const rPairs: Array<[string, string]> = [];
  const seenR = new Set<string>();
  for (const [o, n] of tree.moves) {
    if (tree.original(o) !== null && tree.get(o) === null && tree.original(n) === null && tree.get(n) !== null) {
      const k = `${o}\0${n}`;
      if (!seenR.has(k)) {
        seenR.add(k);
        rPairs.push([o, n]);
        rOld.add(o);
        rNew.add(n);
      }
    }
  }
  for (const p of tree.now.keys()) {
    const was = tree.original(p);
    const now = tree.now.get(p)!;
    if (was === now) continue;
    if (rOld.has(p) || rNew.has(p)) continue;
    rows.push({ key: p, line: `${was === null ? 'A' : now === null ? 'D' : 'M'} ${p}` });
  }
  for (const [o, n] of rPairs) rows.push({ key: n, line: `R ${o} -> ${n}` });
  rows.sort((a, b) => Buffer.compare(Buffer.from(a.key), Buffer.from(b.key)));
  const outLines = rows.map((r) => r.line);
  if (!check) {
    for (const p of tree.now.keys()) {
      const was = tree.original(p);
      const now = tree.now.get(p)!;
      if (was === now) continue;
      if (now === null) rmSync(p, { force: true });
      else {
        mkdirSync(dirname(p), { recursive: true });
        writeFileSync(p, now);
      }
    }
  }
  return { code: 0, out: [...outLines, `ok: ${outLines.length} ${outLines.length === 1 ? 'file' : 'files'}`] };
}

const trialEnv = process.env.MAKEFUN_ENV_URL;
if (trialEnv !== undefined && trialEnv !== '') {
  // A trial: the kit's runner reads the checks from the env and runs this file on each one.
  const { runTrial } = await import('./runner.ts');
  await runTrial(trialEnv);
} else {
  const r = run(process.argv.slice(2));
  writeSync(1, r.out.map((l) => `${l}\n`).join(''));
  process.exitCode = r.code;
}
