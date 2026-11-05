// The element of a loop flows into a nullable field and a nullable local.
// Lean must know the element's type there, or it would take the element to
// be nullable too.
export interface Last {
  readonly value: number | null;
}

export function lastOf(xs: ReadonlyArray<number>): Last {
  let last: Last = { value: null };
  for (const x of xs) {
    last = { value: x };
  }
  return last;
}

export function lastBigint(xs: ReadonlyArray<bigint>, start: bigint | null): bigint | null {
  let last = start;
  for (const x of xs) {
    last = x;
  }
  return last;
}
