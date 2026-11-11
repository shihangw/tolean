// expect: 3:10 a spread '...' needs a value of an interface
export function f(xs: ReadonlyArray<bigint>): boolean {
  return { ...xs } === null;
}
