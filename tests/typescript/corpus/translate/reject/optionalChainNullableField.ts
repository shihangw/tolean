// expect: 6:10 '?.' may not read a nullable field, because the value could be null or undefined
export interface P {
  readonly x: bigint | null;
}
export function f(p: P | null): bigint {
  return p?.x ?? 0n;
}
