// expect: 6:19 'S' would hide the interface S in Lean
// TypeScript keeps types and values apart; Lean does not.
export interface S {
  readonly v: bigint;
}
export function g(S: bigint, x: S): bigint {
  return S + x.v;
}
