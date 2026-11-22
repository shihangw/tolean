// expect: 5:3 push is allowed only onto an owned array
export interface Holder { readonly xs: Array<number>; }
export function f(s: Holder): number {
  const { xs } = s;
  xs.push(1);
  return xs.length;
}
