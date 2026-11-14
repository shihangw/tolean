// expect: 3:3 set, add and delete are allowed only on an owned map or set
function change(m: Map<string, bigint>, other: ReadonlyMap<string, bigint>): boolean {
  m.set('a', 1n);
  return other.has('a');
}

export function f(): boolean {
  const m = new Map<string, bigint>();
  return change(m, m);
}
