// `map` with an arrow function of two parameters becomes `List.mapIdx`. The
// second parameter is the index, a number, as JS passes it.
export interface Entry {
  readonly position: number;
  readonly value: bigint;
}

export function positions(xs: ReadonlyArray<bigint>): ReadonlyArray<number> {
  return xs.map((x, i) => i);
}

export function entries(xs: ReadonlyArray<bigint>): ReadonlyArray<Entry> {
  return xs.map((x, i) => ({ position: i, value: x }));
}

export function shifted(xs: ReadonlyArray<number>, offset: number): ReadonlyArray<number> {
  return xs.map((x: number, i: number) => x + i + offset);
}

export function firsts(xs: ReadonlyArray<bigint>): ReadonlyArray<boolean> {
  return xs.map((x, i) => i === 0);
}

export function sums(rows: ReadonlyArray<ReadonlyArray<bigint>>): ReadonlyArray<ReadonlyArray<number>> {
  return rows.map((row, r) => row.map((x, c) => r + c));
}

export function ignoresIndex(xs: ReadonlyArray<bigint>): ReadonlyArray<bigint> {
  return xs.map((x, i) => x + 1n);
}
