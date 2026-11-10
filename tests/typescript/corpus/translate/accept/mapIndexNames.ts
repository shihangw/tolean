// The certificate of a callback of `map` that takes the index works whatever
// the source names are: a local may be named `Nat`, and the index may have
// the name of one of the certificate's own hypotheses.
export function add(Nat: bigint, xs: ReadonlyArray<bigint>): ReadonlyArray<bigint> {
  return xs.map((x, i) => x + Nat);
}

export function f(xs: ReadonlyArray<bigint>, offset: bigint): ReadonlyArray<bigint> {
  return xs.map((x, hI) => x + offset);
}
