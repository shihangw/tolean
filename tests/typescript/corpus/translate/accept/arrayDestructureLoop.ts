// `for (const [k, v] of xs)` binds the names of the pattern to each element,
// as `const [k, v] = element` does. The fold binds the element to the first
// name, and the body starts with the pattern.
export function weighted(pairs: ReadonlyArray<readonly [bigint, bigint]>): bigint {
  let total = 0n;
  for (const [w, x] of pairs) {
    total += w * x;
  }
  return total;
}

export function seconds(pairs: ReadonlyArray<readonly [string, bigint]>): bigint {
  let total = 0n;
  for (const [, n] of pairs) {
    total += n;
  }
  return total;
}

export function firstPositive(pairs: ReadonlyArray<readonly [string, bigint]>): string {
  for (const [name, score] of pairs) {
    if (score > 0n) {
      return name;
    }
  }
  return '';
}
