// expect: certificates for loops that can throw need a monadic loop invariant
export function sum(xs: ReadonlyArray<bigint>): bigint {
  let result = 0n;
  for (const x of xs) {
    if (x < 0n) {
      throw new Error("negative");
    }
    result += x;
  }
  return result;
}
