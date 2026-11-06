// expect: 3:3 only one default
export function f(a: bigint): bigint {
  switch (a) {
    default:
      return 1n;
    default:
      return 2n;
  }
}
