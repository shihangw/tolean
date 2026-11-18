// expect: 5:25 the source reads a name declared by this pattern before initialization
export interface Pair { readonly a: number; readonly b: number; }
export function f(s: Pair): number {
  if (true) {
    const { a: s, b } = s;
    return s + b;
  } else { return 0; }
}
