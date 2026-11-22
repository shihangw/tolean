// expect: 5:5 arithmetic needs two bigints or two numbers
export function compound(x: bigint): bigint {
  let value = [x][0];
  for (const item of [x]) {
    value += item ** 2n;
  }
  return value ?? 0n;
}
