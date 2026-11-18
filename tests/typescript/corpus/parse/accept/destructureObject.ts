export interface Pair { readonly a: number; readonly b: number; }

const { a } = { a: 1 };

export function swap(o: Pair): number {
  const { a: b, b: a, } = o;
  let { a: x } = o;
  x = x + a;
  return x - b;
}
