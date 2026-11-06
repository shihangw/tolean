// expect: 4:10 an object literal must build an interface
type V = string | bigint;
export function f(): V {
  return { kind: 'a' };
}
