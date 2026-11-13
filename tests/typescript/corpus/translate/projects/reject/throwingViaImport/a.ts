export function checked(n: bigint): bigint {
  if (n < 0n) throw new Error("negative");
  return n;
}
