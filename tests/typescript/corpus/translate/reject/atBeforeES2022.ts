// target: ES2021
// expect: 5:10 the target ES2021 does not have Array.prototype.at
// Array.prototype.at is in ES2022.
export function f(xs: ReadonlyArray<bigint>): bigint {
  return xs.at(0) ?? 0n;
}
