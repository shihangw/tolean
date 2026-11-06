// expect: 3:7 typeof may only test, in an if, a local of a union of primitive types
export function f(x: string): boolean {
  if (typeof x === 'string') return true;
  return false;
}
