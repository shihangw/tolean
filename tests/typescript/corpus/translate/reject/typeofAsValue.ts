// expect: 4:10 typeof may only test, in an if, a local of a union of primitive types
type V = string | bigint;
export function f(v: V): boolean {
  return typeof v === 'string';
}
