// `xs.slice(start, end)` with integer literals becomes `List.drop` and
// `List.take`. A negative bound counts from the end, which the output reads
// on the reversed list.
export function copy(xs: ReadonlyArray<bigint>): ReadonlyArray<bigint> {
  return xs.slice();
}

export function rest(xs: ReadonlyArray<bigint>): ReadonlyArray<bigint> {
  return xs.slice(1);
}

export function middle(xs: ReadonlyArray<string>): ReadonlyArray<string> {
  return xs.slice(1, 3);
}

export function lastTwo(xs: ReadonlyArray<number>): ReadonlyArray<number> {
  return xs.slice(-2);
}

export function dropLast(xs: ReadonlyArray<bigint>): ReadonlyArray<bigint> {
  return xs.slice(0, -1);
}

export function inner(xs: ReadonlyArray<boolean>): ReadonlyArray<boolean> {
  return xs.slice(1, -1);
}

export function between(xs: ReadonlyArray<bigint>): ReadonlyArray<bigint> {
  return xs.slice(-3, -1);
}

export function empty(xs: ReadonlyArray<bigint>): ReadonlyArray<bigint> {
  return xs.slice(3, 1);
}

export function headCount(xs: ReadonlyArray<bigint>): number {
  return xs.slice(0, 2).length;
}

export function tailSums(rows: ReadonlyArray<bigint>): ReadonlyArray<boolean> {
  return rows.slice(1).map((x) => x > 0n);
}
