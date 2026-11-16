// expect: 3:3 an expression statement must assign a let local
export function change(x: { n: bigint }): bigint {
  x.n = 1n;
  return x.n;
}
