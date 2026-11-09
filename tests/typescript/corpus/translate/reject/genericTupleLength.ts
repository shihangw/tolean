// expect: 6:15 the tuple needs 2 elements
function swap<A, B>(p: [A, B]): [B, A] {
  return [p[1], p[0]];
}
export function f(): [bigint, bigint] {
  return swap([1n, 2n, 3n]);
}
