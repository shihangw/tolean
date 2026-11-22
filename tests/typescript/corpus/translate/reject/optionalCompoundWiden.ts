// expect: 4:3 arithmetic needs two bigints or two numbers
export function compound(x: bigint): bigint {
  let value = [x][0];
  value += x ** 2n;
  return value ?? 0n;
}
