export function f(): bigint {
  return (Number.isNaN(NaN) ? null : [1n])?.[0] ?? 0n;
}
