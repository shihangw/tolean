// expect: 3:5 tsc may read this '<' as the start of type arguments
export function comparison(f, x) {
  f < A, B > (x);
}
