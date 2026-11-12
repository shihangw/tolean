export class NotFound extends Error {}

export function checked(n: bigint): bigint {
  if (n < 0n) throw new NotFound("no count");
  return n;
}
