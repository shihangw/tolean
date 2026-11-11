// `const [a, b] = e` iterates `e`, as `for … of` does, and binds each name in
// order. A tuple gives its elements. An array gives optional values, which
// are `undefined` past its end, and a rest element gives the values after the
// places.
export function swap(p: readonly [bigint, string]): readonly [string, bigint] {
  const [n, s] = p;
  return [s, n];
}

export function divmod(a: bigint): readonly [bigint, bigint] {
  return [a / 7n, a % 7n];
}

export function digits(a: bigint): bigint {
  const [q, r] = divmod(a);
  return q + r;
}

export function middle(t: readonly [bigint, bigint, bigint]): bigint {
  const [, b] = t;
  return b;
}

export function firstTwo(xs: ReadonlyArray<bigint>): bigint {
  const [a, b] = xs;
  return (a ?? 0n) + (b ?? 0n);
}

export function rest(xs: ReadonlyArray<bigint>): ReadonlyArray<bigint> {
  const [, ...others] = xs;
  return others;
}

export function third(xs: ReadonlyArray<string>): string {
  const [, , c] = xs;
  return c ?? '';
}

export function split(xs: ReadonlyArray<string>): number {
  const [head, ...tail]: ReadonlyArray<string> = xs;
  return (head ?? '').length + tail.length;
}

function halves(a: bigint): readonly [bigint, bigint] {
  const [q, r] = divmod(a);
  return [q, r];
}

export function nested(a: bigint): bigint {
  const [x, y] = halves(a);
  return x + y;
}
