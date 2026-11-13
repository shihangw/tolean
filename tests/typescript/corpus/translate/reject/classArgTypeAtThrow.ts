// expect: 9:30 the argument does not have the parameter's type
// A number where the parameter is a bigint: the fault is the throw's, not the class's.
class Oops extends Error {
  constructor(readonly n: bigint) {
    super(n > 0n ? "pos" : "neg");
  }
}
export function f(x: bigint): bigint {
  if (x < 0n) throw new Oops(1);
  return x;
}
