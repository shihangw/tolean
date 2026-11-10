// expect: 6:22 a map key must be a bigint, a string, a boolean or a literal union of strings
interface P {
  readonly x: bigint;
}

export function f(m: ReadonlyMap<P, bigint>): bigint {
  return 0n;
}
