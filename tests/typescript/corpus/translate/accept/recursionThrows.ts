// A function that calls itself can throw. A call of itself as the whole value
// of a `const` or a `return` passes the error on, and must still pass a part of
// one parameter.
export interface Node {
  readonly value: bigint;
  readonly next: Node | null;
}

export function sumChecked(n: Node | null): bigint {
  if (n === null) return 0n;
  if (n.value < 0n) throw new Error("a value may not be negative");
  const rest = sumChecked(n.next);
  return n.value + rest;
}

export function lastChecked(n: Node): bigint {
  if (n.value < 0n) throw new Error("a value may not be negative");
  const next = n.next;
  if (next === null) return n.value;
  return lastChecked(next);
}
