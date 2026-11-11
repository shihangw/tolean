// expect: 3:16 the argument of 'at' must be an integer literal, such as xs.at(-1)
export function f(xs: ReadonlyArray<bigint>, i: number): bigint {
  return xs.at(i) ?? 0n;
}
