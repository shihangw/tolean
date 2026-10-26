import { describe, expect, test } from 'vitest';

import { TranslateError, translateSource } from './translate.ts';

const translate = (text: string): string =>
  translateSource({ fileName: 'input.ts', text, namespace: 'Test' });

describe('translateSource', () => {
  // Soundness rests on refusing what the embedding cannot model. Each row is
  // a construct whose JS meaning a shallow Lean translation would get wrong.
  test.each([
    [
      'reassigned parameter',
      'export function f(x: bigint): bigint { x = 1n; return x; }',
    ],
    [
      'push onto an array the function does not own',
      'export function f(xs: Array<bigint>): bigint { xs.push(1n); return 0n; }',
    ],
    [
      'bigint division by a value that may be 0n, where JS throws',
      'export function f(a: bigint, b: bigint): bigint { return a / b; }',
    ],
    [
      'bigint division by 0n',
      'export function f(a: bigint): bigint { return a % 0n; }',
    ],
    [
      'number division, which no law covers',
      'export function f(a: number): number { return a / 2; }',
    ],
    [
      'object identity',
      'interface P { readonly x: bigint }\nexport function f(a: P, b: P): boolean { return a === b; }',
    ],
    [
      'break out of a loop',
      'export function f(xs: ReadonlyArray<bigint>): bigint { let s = 0n; for (const x of xs) { if (x > 0n) { break; } s += x; } return s; }',
    ],
    [
      'a fractional number literal, which no integer law covers',
      'export function f(): number { return 0.5; }',
    ],
    [
      'an assignment hidden in a null test whose answer is already known',
      'export function f(x: bigint): bigint { const ignored = (x = 1n) === null; return x; }',
    ],
    [
      'a Number predicate on a value that may be null, which TypeScript allows',
      'export function f(x: number | null): boolean { return Number.isFinite(x); }',
    ],
    [
      'the global isNaN, which converts its argument to a number first',
      'export function f(x: number): boolean { return isNaN(x); }',
    ],
    [
      '=== between nullable values',
      'export function f(a: number | null, b: number | null): boolean { return a === b; }',
    ],
    [
      'recursion, which needs a termination proof',
      'export function f(x: bigint): bigint { return f(x); }',
    ],
    [
      'an alias of an owned array, which a later push mutates in JS only',
      'export function f(): ReadonlyArray<bigint> { const xs: Array<bigint> = []; const alias = xs; xs.push(1n); return alias; }',
    ],
    [
      'a loop over an owned array it pushes to, which JS iterates further',
      'export function f(): ReadonlyArray<bigint> { const xs: Array<bigint> = []; xs.push(1n); for (const x of xs) { xs.push(x); } return xs; }',
    ],
    [
      'mutable interface field',
      'interface P { x: bigint }\nexport function f(p: P): bigint { return p.x; }',
    ],
  ])('rejects %s', (_name, source) => {
    expect(() => translate(source)).toThrow(TranslateError);
  });

  test('types bigint literals as Int, so Lean never defaults them to Nat', () => {
    // As a Nat, `0 - 1` is 0 and this would be false in Lean, true in JS.
    const lean = translate(
      'export function f(): boolean { return 0n - 1n < 0n; }',
    );

    expect(lean).toContain('((0 : Int) - (1 : Int)) < (0 : Int)');
  });

  test('keeps number abstract and turns a null check into a match', () => {
    // Never Lean's Float: number operations go through the JSNumber class.
    const lean = translate(
      'export function f(a: number, b: number | null): boolean { return b === null || a < b; }',
    );

    expect(lean).toContain('[JSNumber N]');
    expect(lean).toContain(
      'match b with | none => true | some b => (JSNumber.lt a b)',
    );
  });

  test('narrows an if on null, and updates a number through JSNumber', () => {
    const lean = translate(
      'export function f(x: number | null, y: number): number { let total = y; if (x !== null) { total += x; } return total; }',
    );

    expect(lean).toContain('| some x =>');
    expect(lean).toContain('(JSNumber.add total x)');
  });

  test('fixes a null test on a value TypeScript has already narrowed', () => {
    // After the guard, x is the value inside the Option, so x === null is false.
    const lean = translate(
      'export function f(x: bigint | null): boolean { if (x === null) return true; return x === null || x > 0n; }',
    );

    expect(lean).toContain('(false || decide (x > (0 : Int)))');
  });

  test('maps Number.isNaN, NaN and ±Infinity to the JSNumber model', () => {
    const lean = translate(
      'export function f(x: number): boolean { return Number.isNaN(x) || x < -Infinity || Number.isNaN(NaN); }',
    );

    expect(lean).toContain('(JSNumber.isNaN x)');
    expect(lean).toContain('(JSNumber.negInf (N := N))');
    expect(lean).toContain('(JSNumber.nan (N := N))');
  });

  test('treats a union of number literals, such as c ? 0 : 1, as a number', () => {
    const lean = translate(
      'export function f(flag: boolean, x: number): boolean { return Number.isFinite((flag ? 0 : 1) + x); }',
    );

    expect(lean).toMatch(/JSNumber\.isFinite \(+JSNumber\.add/);
  });

  test('uses the number model when only NaN or Infinity appear', () => {
    const lean = translate(
      'export function f(): boolean { return Number.isNaN(NaN); }',
    );

    expect(lean).toContain('import tolean.TypeScript.Spec.Number');
    expect(lean).toContain('[JSNumber N]');
  });

  test('accepts === on booleans, which TypeScript types as a union', () => {
    expect(() =>
      translate(
        'export function f(a: boolean, b: boolean): boolean { return a === b; }',
      ),
    ).not.toThrow();
  });

  test('writes bigint / and % by a nonzero literal as Int.tdiv and Int.tmod', () => {
    // Both truncate toward zero, as JS does: -7n / 2n is -3n, -7n % 2n is -1n.
    const lean = translate(
      'export function f(a: bigint): bigint { return a / 2n + a % -3n; }',
    );

    expect(lean).toContain('(Int.tdiv a ((2 : Int)))');
    expect(lean).toContain('(Int.tmod a ((-(3 : Int))))');
  });

  test('names N in calls, so a callee whose signature lacks N elaborates', () => {
    const lean = translate(
      'function g(x: bigint): bigint { return Number.isNaN(NaN) ? x : x; }\nexport function f(x: bigint): bigint { return g(x); }',
    );

    expect(lean).toContain('(g (N := N) x)');
  });

  test('writes bigint literals in decimal', () => {
    const lean = translate('export function f(): bigint { return 0x1fn; }');

    expect(lean).toContain('(31 : Int)');
  });

  test('names the tolean version and the target edition in the header', () => {
    const lean = translateSource({
      fileName: 'input.ts',
      text: 'export function f(): boolean { return true; }',
      namespace: 'Test',
      target: 'ES2022',
    });

    expect(lean).toMatch(/^-- Generated by tolean \d+\.\d+\.\d+ for ES2022 from input\.ts\./);
  });

  test.each([
    ['bigint', 'ES2019', 'export function f(): bigint { return 1n; }'],
    ['numeric separators', 'ES2020', 'export function f(): number { return 1_000; }'],
    ["'??'", 'ES2019', 'export function f(a: number | null): number { return a ?? 0; }'],
  ] as const)('refuses %s below the edition that added it (target %s)', (_name, target, text) => {
    expect(() =>
      translateSource({ fileName: 'input.ts', text, namespace: 'Test', target }),
    ).toThrow(/does not have/);
  });

  test('turns a loop over owned locals into a fold over their tuple', () => {
    const lean = translate(
      'export function f(xs: ReadonlyArray<bigint>): bigint { let s = 0n; for (const x of xs) { s += x; } return s; }',
    );

    expect(lean).toContain('(fun s x =>');
    expect(lean).toContain('let s := s + x');
  });
});
