// expect: 3:7 tsc may read this '<' as the start of type arguments
export function comparison(a, b, c, d) {
  f(a < b, c > d);
}
