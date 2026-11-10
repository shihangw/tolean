// expect: 3:13 'new' is supported only before a name
export function f() {
  return new.target;
}
