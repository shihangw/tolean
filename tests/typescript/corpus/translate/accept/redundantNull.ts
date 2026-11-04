// `Maybe | null` is `Maybe` when `Maybe` may be null already.
type Maybe = bigint | null;

export function present(x: Maybe | null): boolean {
  return x !== null;
}

export function plusOne(x: Maybe | null): bigint {
  if (x === null) return 0n;
  return x + 1n;
}
