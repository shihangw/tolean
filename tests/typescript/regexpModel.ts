import { spawnSync } from 'node:child_process';
import { mkdtempSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { fileURLToPath } from 'node:url';

type Pattern = { source: string; lean: string };

/** Check the matcher directly until regex literals reach the interpreter.
 * Each generated pattern has both ECMAScript source and a Lean pattern tree.
 * Inputs include lone surrogates, which Lean string literals cannot express.
 */
export function checkRegexpModel(seed: number): void {
  let state = seed >>> 0 || 1;
  const pick = (n: number): number => {
    state ^= state << 13;
    state ^= state >>> 17;
    state ^= state << 5;
    return (state >>> 0) % n;
  };
  const units = [97, 98, 99, 48, 32, 10, 13, 0x2028, 0x2029, 0xd800, 0xdc00];
  const literal = (u: number): Pattern => ({
    source: `\\u${u.toString(16).padStart(4, '0')}`,
    lean: `(.unit ${u})`,
  });
  const sequence = (a: Pattern, b: Pattern): Pattern => ({
    source: `(?:${a.source}${b.source})`,
    lean: `(.seq ${a.lean} ${b.lean})`,
  });
  const alternative = (a: Pattern, b: Pattern): Pattern => ({
    source: `(?:${a.source}|${b.source})`,
    lean: `(.alt ${a.lean} ${b.lean})`,
  });
  const repeat = (a: Pattern, minimum: number, maximum: number | null): Pattern => ({
    source: `(?:${a.source}){${minimum},${maximum ?? ''}}`,
    lean: `(.repeat ${a.lean} ${minimum} ${maximum === null ? 'none' : `(some ${maximum})`})`,
  });
  const text = (s: string): string =>
    `⟨[${Array.from({ length: s.length }, (_, i) => s.charCodeAt(i)).join(', ')}]⟩`;
  const output = [
    'import tolean.TypeScript.Spec.RegExp',
    'open tolean.TypeScript',
    'open tolean.TypeScript.JSRegExp',
    'def observe (input : JSString) (p : Pattern) (count : Nat) :',
    '    Option (Nat × Nat × List (Option JSString)) :=',
    '  (search input p count).map fun (start, result) =>',
    '    (start, result.pos.val, result.captures.map fun capture =>',
    '      capture.map fun (lo, hi) => ⟨(input.units.drop lo).take (hi - lo)⟩)',
  ];
  const add = (p: Pattern, s: string, captures: number): void => {
    const found = new RegExp(p.source).exec(s);
    const expected = found === null ? 'none' :
      `some (${found.index}, ${found.index + found[0].length}, [${
        found.slice(1).map(c => c === undefined ? 'none' : `(some ${text(c)})`).join(', ')
      }])`;
    output.push(`#guard observe ${text(s)} ${p.lean} ${captures} = ${expected}`);
    output.push(`#guard test ${text(s)} ${p.lean} = ${found !== null}`);
  };
  let captures = 0;
  const capture = (body: () => Pattern): Pattern => {
    const index = captures++;
    const p = body();
    return { source: `(${p.source})`, lean: `(.capture ${index} ${p.lean})` };
  };
  const generate = (depth: number): Pattern => {
    if (depth === 0) {
      switch (pick(6)) {
        case 0: return { source: '(?:)', lean: '.empty' };
        case 1: return { source: '.', lean: '.dot' };
        case 2: return { source: '^', lean: '.beginInput' };
        case 3: return { source: '$', lean: '.endInput' };
        case 4: {
          const negated = pick(2) === 0;
          return {
            source: `[${negated ? '^' : ''}a-c0-2]`,
            lean: `(.charClass ${negated} [(97, 99), (48, 50)])`,
          };
        }
        default: return literal(units[pick(units.length)]);
      }
    }
    switch (pick(5)) {
      case 0: return sequence(generate(depth - 1), generate(depth - 1));
      case 1: return alternative(generate(depth - 1), generate(depth - 1));
      case 2: {
        const minimum = pick(3);
        const maximum = pick(2) === 0 ? null : minimum + pick(3);
        return repeat(generate(depth - 1), minimum, maximum);
      }
      case 3: return capture(() => generate(depth - 1));
      default: return generate(0);
    }
  };
  const a = literal(97);
  const b = literal(98);
  const c = literal(99);
  add(sequence(alternative(a, sequence(a, b)), c), 'abc', 0);
  add(sequence(repeat(a, 0, null), a), 'aaa', 0);
  add(repeat({ source: '(?:)', lean: '.empty' }, 3, null), '', 0);
  add(sequence({ source: '^', lean: '.beginInput' },
    sequence({ source: '.', lean: '.dot' }, { source: '$', lean: '.endInput' })), '😀', 0);
  add(sequence(a, { source: '$', lean: '.endInput' }), 'a\n', 0);
  captures = 0;
  const repeatedCaptures = repeat(capture(() =>
    alternative(capture(() => a), capture(() => b))), 1, null);
  add(repeatedCaptures, 'ab', captures);
  for (let i = 0; i < 400; i++) {
    captures = 0;
    const p = generate(3);
    let s = '';
    const length = pick(8);
    for (let j = 0; j < length; j++) s += String.fromCharCode(units[pick(units.length)]);
    add(p, s, captures);
  }
  const directory = mkdtempSync(join(tmpdir(), 'tolean-regexp-'));
  try {
    const path = join(directory, 'Cases.lean');
    writeFileSync(path, output.join('\n') + '\n');
    const checked = spawnSync('lake', ['env', 'lean', path], {
      cwd: fileURLToPath(new URL('../../', import.meta.url)),
      encoding: 'utf8',
      timeout: 180_000,
      maxBuffer: 16 * 1024 * 1024,
    });
    if (checked.error || checked.status !== 0) {
      throw new Error(`RegExp model disagrees with Node (seed ${seed}):\n` +
        `${checked.error ?? ''}\n${checked.stdout}\n${checked.stderr}`);
    }
  } finally {
    rmSync(directory, { recursive: true, force: true });
  }
}
