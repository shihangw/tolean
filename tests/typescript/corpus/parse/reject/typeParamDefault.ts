// expect: 2:14 type parameters with a default are not supported
function f<T = string>(x: T): T {
  return x;
}
