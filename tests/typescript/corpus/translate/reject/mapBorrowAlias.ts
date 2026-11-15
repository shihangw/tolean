// expect: 3:3 set, add and delete are allowed only on an owned map or set
function change(m: Map<string, bigint>): boolean {
  m.set('a', 1n);
  return true;
}

export function f(): boolean {
  const m = new Map<string, bigint>();
  const alias = m;
  const done = change(m);
  return alias.has('a');
}
