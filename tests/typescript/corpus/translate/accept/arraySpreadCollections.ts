// A spread iterates its operand (ECMA-262 §13.2.4.1), as `for … of` does: a
// set gives its elements and a map its entries `[key, value]`, each in the
// order of insertion.
export function elements(s: Set<string>): ReadonlyArray<string> {
  return [...s];
}

export function entries(m: Map<string, bigint>): ReadonlyArray<[string, bigint]> {
  return [...m];
}

export function withFirst(first: string, s: Set<string>): ReadonlyArray<string> {
  return [first, ...s];
}

export function both(s: Set<string>, xs: ReadonlyArray<string>): ReadonlyArray<string> {
  return [...xs, ...s, ...xs];
}
