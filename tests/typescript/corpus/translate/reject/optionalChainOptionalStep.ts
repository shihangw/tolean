// expect: 9:10 'next' may be undefined, so the property after it needs '?.' too
export interface Q {
  readonly y: bigint;
}
export interface P {
  readonly next?: Q;
}
export function f(p: P | null): bigint {
  return p?.next.y ?? 0n;
}
