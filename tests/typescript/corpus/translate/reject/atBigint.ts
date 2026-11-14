// expect: 3:16 the argument of 'at' must be a number
export function f(xs: ReadonlyArray<bigint>, i: bigint): bigint {
  return xs.at(i) ?? 0n;
}
