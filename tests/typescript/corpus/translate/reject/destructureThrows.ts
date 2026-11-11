// expect: 9:18 a pattern may not take the value of a call that can throw
function pair(a: bigint): readonly [bigint, bigint] {
  if (a < 0n) {
    throw new Error('negative');
  }
  return [a, a];
}
export function f(a: bigint): bigint {
  const [x, y] = pair(a);
  return x + y;
}
