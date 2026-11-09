// expect: 2:14 expected a type parameter, found '>'
function f<T,>(x: T): T {
  return x;
}
