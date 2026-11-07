// expect: 2:1 the type parameter 'T' is declared twice
export function f<T, T>(x: T): T {
  return x;
}
