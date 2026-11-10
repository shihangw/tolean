// expect: 3:13 new Set needs the type of its elements
export function f(): bigint {
  const s = new Set();
  return 0n;
}
