// expect: 4:11 expected an expression, found '...'
// A spread is an element of an array or an argument, not an expression.
export function f(xs: ReadonlyArray<bigint>) {
  return (...xs);
}
