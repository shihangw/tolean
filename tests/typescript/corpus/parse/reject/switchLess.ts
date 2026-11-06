// expect: 4:5 '<' or '<<'
export function f(a: bigint, b: bigint): bigint {
  switch (a) {
    case a < b ? 1n : 2n:
      return 1n;
  }
  return 0n;
}
