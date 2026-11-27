// expect: 9:17 an owned map or set may be read only through get, has and size, or in the return value
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
