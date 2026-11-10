// `xs.reduce((acc, x) => e, init)` becomes `List.foldl`. The value so far has
// the type of the initial value.
export interface Line {
  readonly qty: bigint;
  readonly price: bigint;
}

export function sum(xs: ReadonlyArray<bigint>): bigint {
  return xs.reduce((acc, x) => acc + x, 0n);
}

export function total(lines: ReadonlyArray<Line>): bigint {
  return lines.reduce((acc: bigint, l: Line) => acc + l.qty * l.price, 0n);
}

export function count(xs: ReadonlyArray<string>, name: string): bigint {
  return xs.reduce((n, x) => (x === name ? n + 1n : n), 0n);
}

export function allPositive(xs: ReadonlyArray<number>): boolean {
  return xs.reduce((ok, x) => ok && x > 0, true);
}

export function largest(xs: ReadonlyArray<bigint>, start: bigint): bigint {
  return xs.reduce((best, x) => (x > best ? x : best), start);
}

export function sums(rows: ReadonlyArray<ReadonlyArray<bigint>>): ReadonlyArray<bigint> {
  return rows.map((r) => r.reduce((acc, x) => acc + x, 0n));
}

export function totalIn(xs: ReadonlyArray<bigint>, factor: bigint): bigint {
  let t = 0n;
  for (const x of xs) {
    t = t + x;
  }
  return xs.reduce((acc, x) => acc + x * factor, t);
}
