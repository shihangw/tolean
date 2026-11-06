// expect: 6:10 the left side of '?.' is never null or undefined here, so '?.' does nothing; use '.'
export interface P {
  readonly x: bigint;
}
export function f(p: P): bigint {
  return p?.x ?? 0n;
}
