export function withZero(xs: ReadonlyArray<bigint>): ReadonlyArray<bigint> {
  const out: Array<bigint> = [0n];
  for (const x of xs) {
    out.push(x);
  }
  return out;
}
