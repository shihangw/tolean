// `...e` spreads the values of `e` into an array literal or into the
// arguments of a call or a `new`.
export function arrays(xs: ReadonlyArray<bigint>, ys: ReadonlyArray<bigint>, b: boolean) {
  const a = [...xs];
  const c = [0n, ...xs, 1n];
  const d = [...xs, ...ys];
  const e = [...(b ? xs : ys)];
  const f = [...xs.map((x) => x + 1n), ...[1n, 2n]];
  const g = [...[...xs]];
  const h = [...xs.filter((x) => x > 0n), ys.length];
  return [a, c, d, e, f, g, h];
}

export function calls(xs: ReadonlyArray<bigint>) {
  sum(...xs);
  sum(1n, ...xs, 2n);
  return new Set<bigint>(...[xs]);
}

function sum(a: bigint, b?: bigint, c?: bigint): bigint {
  return a;
}
