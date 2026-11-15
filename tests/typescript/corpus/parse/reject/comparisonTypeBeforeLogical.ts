// expect: 3:5 tsc may read this '<' as the start of type arguments
export function comparison(a, b, c, d) {
  a < b > c && d;
}
