// expect: 3:13 only new Map() and new Set() are supported
export function f(): bigint {
  const d = new Date(0);
  return 0n;
}
