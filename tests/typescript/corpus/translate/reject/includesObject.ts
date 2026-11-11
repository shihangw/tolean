// expect: 6:10 'includes' needs an array of numbers, bigints, booleans, strings or a literal union
export interface Box {
  readonly n: bigint;
}
export function f(xs: ReadonlyArray<Box>, b: Box): boolean {
  return xs.includes(b);
}
