// expect: 2:14 type parameters with a constraint are not supported
function f<T extends string>(x: T): T {
  return x;
}
