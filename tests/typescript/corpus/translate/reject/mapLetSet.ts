// expect: 4:3 set and delete are allowed only on an owned map
export function f(): Map<string, bigint> {
  let m = new Map<string, bigint>();
  m.set('a', 1n);
  return m;
}
