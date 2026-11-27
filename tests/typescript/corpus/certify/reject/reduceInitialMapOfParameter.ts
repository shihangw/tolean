// expect: builds a Map or Set from a list the certificate cannot see
export function f(xs: ReadonlyArray<bigint>, ys: ReadonlyArray<readonly [string, bigint]>): bigint {
  return xs.reduce((a, x) => a + x, new Map<string, bigint>(ys).get("k") ?? 0n);
}
