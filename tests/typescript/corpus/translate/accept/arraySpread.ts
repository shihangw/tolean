// An array literal with a spread, `[...xs, x]`, becomes `xs ++ [x]`. A run of
// elements between spreads becomes one list literal, and `[...xs]` is `xs`.
export function append(xs: ReadonlyArray<bigint>, x: bigint): ReadonlyArray<bigint> {
  return [...xs, x];
}

export function prepend(x: bigint, xs: ReadonlyArray<bigint>): ReadonlyArray<bigint> {
  return [x, ...xs];
}

export function concat(xs: ReadonlyArray<bigint>, ys: ReadonlyArray<bigint>): ReadonlyArray<bigint> {
  return [...xs, ...ys];
}

export function around(xs: ReadonlyArray<string>): ReadonlyArray<string> {
  return ['(', '[', ...xs, ']', ')'];
}

export function copy(xs: ReadonlyArray<bigint>): ReadonlyArray<bigint> {
  return [...xs];
}

export function sum(xs: ReadonlyArray<bigint>, ys: ReadonlyArray<bigint>): bigint {
  const all = [...xs, ...ys];
  return all.reduce((acc, x) => acc + x, 0n);
}

export function literal(): ReadonlyArray<bigint> {
  return [...[1n, 2n], 3n];
}

export function maybe(xs: ReadonlyArray<bigint | null>, x: bigint): ReadonlyArray<bigint | null> {
  return [...xs, x, null];
}
