// A sort by number keys. A file with one gets no certificate yet, because its
// claim needs the precondition that no key is NaN, and for a difference that
// every key is finite.
interface Event {
  readonly time: number;
  readonly kind: string;
}

// A difference of number keys: the comparator is consistent when every key
// is finite.
export function chronological(events: ReadonlyArray<Event>): Event[] {
  return events.toSorted((a, b) => a.time - b.time);
}

export function latestFirst(events: ReadonlyArray<Event>): Event[] {
  return [...events].sort((a, b) => b.time - a.time);
}

// A difference as the last comparison of a chain.
export function byKindThenTime(events: ReadonlyArray<Event>): Event[] {
  return events.toSorted((a, b) => (a.kind < b.kind) ? -1 : (a.kind > b.kind) ? 1 : a.time - b.time);
}

// A comparison of number keys, which is consistent when no key is NaN.
export function numbers(xs: ReadonlyArray<number>): number[] {
  return xs.toSorted((x, y) => (x < y) ? -1 : (x > y) ? 1 : 0);
}

// sort on a spread with an element.
export function withZero(xs: ReadonlyArray<number>): number[] {
  return [...xs, 0].sort((x, y) => x - y);
}
