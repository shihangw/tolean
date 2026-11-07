// expect: 3:22 a Record type needs a name
type Kind = 'a' | 'b';
export function f(r: Record<Kind, bigint>, k: Kind): bigint {
  return r[k];
}
