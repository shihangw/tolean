// expect: 7:1 a function may change only an array, a map or a set that it makes in a const
function change(m: Map<string, bigint>, other: ReadonlyMap<string, bigint>): boolean {
  m.set('a', 1n);
  return other.has('a');
}

export function f(): boolean {
  const m = new Map<string, bigint>();
  const r = change(m, m);
  return r;
}
