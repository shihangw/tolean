// expect: 7:3 where more than one member of the union is left, a further test of its tag must come right after, as in a chain of 'if (x.kind === 'a') return …'
interface A { readonly type: 'a'; readonly x: bigint; }
interface B { readonly type: 'b'; }
interface C { readonly type: 'c'; readonly y: bigint; }
type E = A | B | C;
export function f(e: E, n: bigint): bigint {
  if (e.type === 'a') return e.x;
  const m = n + 1n;
  if (e.type === 'b') return m;
  return e.y;
}
