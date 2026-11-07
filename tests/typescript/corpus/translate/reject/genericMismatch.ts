// expect: 6:20 the argument does not have the parameter's type
function first<T>(a: T, b: T): T {
  return a;
}
export function f(): bigint {
  return first(1n, 'a');
}
