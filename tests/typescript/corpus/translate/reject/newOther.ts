// expect: 3:13 only new Map() is supported
export function f(): bigint {
  const d = new Date(0);
  return 0n;
}
