// `x ??= e` assigns `e` only when `x` is null, and JS evaluates `e` only then.
export function orDefault(x: bigint | null, d: bigint): bigint | null {
  let y = x;
  y ??= d;
  return y;
}

export function firstSet(a: bigint | null, b: bigint | null): bigint | null {
  let r: bigint | null = null;
  r ??= a;
  r ??= b;
  return r;
}

export function total(xs: ReadonlyArray<bigint | null>, d: bigint): bigint {
  let sum = 0n;
  for (const x of xs) {
    let v = x;
    v ??= d;
    sum += v ?? 0n;
  }
  return sum;
}
