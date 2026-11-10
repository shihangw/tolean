// expect: 4:13 an owned map or set may be read only through get, has and size
export function f(): boolean {
  const s = new Set<string>();
  const t = s;
  return t.has('a');
}
