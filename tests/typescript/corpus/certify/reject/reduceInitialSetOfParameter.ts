// expect: builds a Map or Set from a list the certificate cannot see
export function f(xs: ReadonlyArray<boolean>, ys: ReadonlyArray<bigint>): boolean {
  return xs.reduce((a, x) => a || x, new Set<bigint>(ys).has(0n));
}
