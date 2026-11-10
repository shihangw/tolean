// expect: 3:13 new Map needs the types of its keys and values
export function f(): bigint {
  const m = new Map();
  return 0n;
}
