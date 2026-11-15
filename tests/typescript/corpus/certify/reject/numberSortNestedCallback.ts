// expect: number sorts inside callback or loop bodies need element or state preconditions
export function f(xs: ReadonlyArray<number>, ys: ReadonlyArray<number>): number[][] {
  return ys.map(_y => xs.toSorted((a, b) => a - b));
}
