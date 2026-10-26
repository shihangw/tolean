/**
 * Print the modules that the given roots import, transitively, one per line.
 * LEAN_SRC_PATH lists the source roots to search, separated by colons.
 *
 *   LEAN_SRC_PATH=.:../..:$(lean --print-prefix)/src/lean node closure.ts Web
 */
import { existsSync, readFileSync } from 'node:fs';
import path from 'node:path';

const roots = (process.env.LEAN_SRC_PATH ?? '').split(':').filter(Boolean);
const find = (m: string) => roots.map((r) => path.join(r, ...m.split('.')) + '.lean').find((p) => existsSync(p));

const seen = new Set<string>();
const stack = process.argv.slice(2);
while (stack.length > 0) {
  const m = stack.pop()!;
  if (seen.has(m)) continue;
  seen.add(m);
  const file = find(m);
  if (file == null) throw new Error(`no source for ${m}`);
  const src = readFileSync(file, 'utf8');
  for (const [, im] of src.matchAll(/^(?:public\s+|meta\s+)*import\s+(?:all\s+)?([\w.«»]+)/gm)) stack.push(im!);
  // Every module imports Init, unless it starts with `prelude`.
  if (!/^\s*prelude\b/m.test(src)) stack.push('Init');
}
console.log([...seen].sort().join('\n'));
