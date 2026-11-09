// expect: 10:10 only fields of interfaces
// Parentheses end the chain, so `(p?.q).y` reads `.y` of `undefined` when `p` is null.
export interface Q {
  readonly y: bigint;
}
export interface P {
  readonly q: Q;
}
export function f(p: P | null): bigint {
  return (p?.q).y;
}
