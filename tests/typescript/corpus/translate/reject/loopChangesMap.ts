// expect: 4:19 a loop may not change the map or set that it runs over
export function f(): Map<string, bigint> {
  const m = new Map<string, bigint>();
  for (const e of m) {
    m.delete(e[0]);
  }
  return m;
}
