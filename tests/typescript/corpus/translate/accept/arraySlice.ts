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

// A callback on a slice reads the elements of the slice: from the start,
// between two bounds, and from the end.
export function laterPlusOne(xs: ReadonlyArray<bigint>): ReadonlyArray<bigint> {
  return xs.slice(2).map((x) => x + 1n);
}

export function middleBig(xs: ReadonlyArray<bigint>): ReadonlyArray<bigint> {
  return xs.slice(1, 3).filter((x) => x > 0n);
}

export function lastPlusOne(xs: ReadonlyArray<bigint>): ReadonlyArray<bigint> {
  return xs.slice(-2).map((x) => x + 1n);
}

export function innerAny(xs: ReadonlyArray<bigint>): boolean {
  return xs.slice(1, -1).some((x) => x < 0n);
}

// A negative start with an end that is not negative counts the start back
// from the length of the array.
export function window(xs: ReadonlyArray<bigint>): ReadonlyArray<bigint> {
  return xs.slice(-2, 3);
}

export function windowSum(xs: ReadonlyArray<bigint>): bigint {
  return xs.slice(-3, 2).reduce((sum, x) => sum + x, 0n);
}
