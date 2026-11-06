// expect: 4:7 typeof may only test, in an if, a local of a union of primitive types against one of its members
type V = string | bigint;
export function f(v: V): bigint {
  if (typeof v === 'number') return 1n;
  return 0n;
}
