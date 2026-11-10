// `includes` on an array literal. The certificate compares the value with
// each element by `===`, so it must reduce strict equality on primitives once
// the literal list has reduced.
export function isOne(x: bigint): boolean {
  return [1n].includes(x);
}

export function anyOne(xs: ReadonlyArray<bigint>): boolean {
  return xs.reduce((a, x) => a || [1n].includes(x), false);
}

export function isSmall(x: bigint): boolean {
  return [0n, 1n, 2n].includes(x);
}
