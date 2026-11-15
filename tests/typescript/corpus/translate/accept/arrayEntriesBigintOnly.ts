export function largest(xs: ReadonlyArray<bigint>): bigint | null {
  let value = 1n;
  for (const [index, element] of xs.entries()) {
    if (value < element) break;
    value = element ** 3n;
  }
  return value;
}
