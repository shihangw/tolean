// target: ES2022
// expect: 5:10 the target ES2022 does not have Array.prototype.findLast
// Array.prototype.findLast is in ES2023.
export function f(xs: ReadonlyArray<bigint>): bigint {
  return xs.findLast((x) => x > 0n) ?? 0n;
}
