// expect: 9:10 a chain after '?.', such as a?.b.c, is not supported
export interface Q {
  readonly y: bigint;
}
export interface P {
  readonly q: Q;
}
export function f(p: P | null): bigint {
  return p?.q.y ?? 0n;
}
