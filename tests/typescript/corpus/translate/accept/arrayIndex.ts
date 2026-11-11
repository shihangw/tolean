// `xs.length` is a number. `xs[i]` and `xs.at(k)` are the element or
// `undefined`, so they have the type of an optional field.
export interface Point {
  readonly x: bigint;
  readonly y: bigint;
}

export function count(xs: ReadonlyArray<bigint>): number {
  return xs.length;
}

export function isEmpty(xs: ReadonlyArray<string>): boolean {
  return xs.length === 0;
}

export function first(xs: ReadonlyArray<bigint>): bigint {
  return xs[0] ?? 0n;
}

export function second(xs: ReadonlyArray<bigint>): bigint | null {
  const v = xs[1];
  if (v === undefined) {
    return null;
  }
  return v;
}

export function nth(xs: ReadonlyArray<string>, i: number): string {
  return xs[i] ?? '';
}

export function hasNth(xs: ReadonlyArray<number>, i: number): boolean {
  return xs[i] !== undefined;
}

export function last(xs: ReadonlyArray<bigint>): bigint {
  return xs.at(-1) ?? 0n;
}

export function secondToLast(xs: ReadonlyArray<bigint>): bigint {
  return xs.at(-2) ?? 0n;
}

export function head(xs: ReadonlyArray<boolean>): boolean {
  return xs.at(0) ?? false;
}

export function firstX(ps: ReadonlyArray<Point>): bigint {
  return ps[0]?.x ?? 0n;
}

export function lengths(rows: ReadonlyArray<ReadonlyArray<bigint>>): ReadonlyArray<number> {
  return rows.map((r) => r.length);
}

export function addFirst(xs: ReadonlyArray<bigint>, ys: ReadonlyArray<bigint>): bigint {
  let total = 0n;
  for (const x of xs) {
    total = total + x + (ys[0] ?? 0n);
  }
  return total;
}
