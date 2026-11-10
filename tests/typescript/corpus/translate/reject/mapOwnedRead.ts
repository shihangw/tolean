// expect: 4:13 an owned map or set may be read only through get, has and size
export function f(): bigint {
  const m = new Map<string, bigint>();
  const n = m;
  return n.get('a') ?? 0n;
}
