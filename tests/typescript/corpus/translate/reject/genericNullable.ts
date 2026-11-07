// expect: 6:10 the arguments do not fix the type parameter T of 'identity'
function identity<T>(x: T): T {
  return x;
}
export function f(n: bigint | null): bigint | null {
  return identity(n);
}
