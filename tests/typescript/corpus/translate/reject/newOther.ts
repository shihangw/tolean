// expect: 3:13 only new Date(t), new Map() and new Set() are supported
export function f(): bigint {
  const d = new WeakMap();
  return 0n;
}
