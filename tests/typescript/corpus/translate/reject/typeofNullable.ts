// expect: 4:7 test a nullable value against null first
type V = string | bigint;
export function f(v: V | null): bigint {
  if (typeof v === 'string') return 1n;
  return 0n;
}
