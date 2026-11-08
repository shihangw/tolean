// expect: 6:10 only an array has this method
export interface Box {
  readonly n: bigint;
}
export function f(b: Box): boolean {
  return b.some(x => x);
}
