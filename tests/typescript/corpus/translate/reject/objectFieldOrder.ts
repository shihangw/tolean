// expect: 7:10 write the fields in the order that Pair declares them: a, b
interface Pair {
  readonly a: bigint;
  readonly b: bigint;
}
export function make(x: bigint): Pair {
  return { b: x, a: x + 1n };
}
