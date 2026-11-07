// expect: 3:10 the tuple needs 2 elements
export function f(a: bigint): [bigint, bigint] {
  return [a];
}
