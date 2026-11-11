// `const out: Array<T> = [...xs]` copies `xs` into a new array, which the
// function owns and may push to.
export function withLast(xs: ReadonlyArray<bigint>, last: bigint): ReadonlyArray<bigint> {
  const out: Array<bigint> = [...xs];
  out.push(last);
  return out;
}

export function evens(xs: ReadonlyArray<bigint>, seed: ReadonlyArray<bigint>): ReadonlyArray<bigint> {
  const out: bigint[] = [0n, ...seed];
  for (const x of xs) {
    if (x % 2n === 0n) {
      out.push(x);
    }
  }
  return out;
}
