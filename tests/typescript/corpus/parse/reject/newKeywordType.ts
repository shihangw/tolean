// expect: 3:10 'new' is supported only before a name
export function f() {
  return new number();
}
