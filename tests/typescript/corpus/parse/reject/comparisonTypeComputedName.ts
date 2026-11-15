// expect: 3:5 tsc may read this '<' as the start of type arguments
export function comparison(f, a, b, x) {
  f < { [a && b]: T } > (x);
}
