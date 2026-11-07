// expect: 6:10 the arguments do not fix the type parameter T of 'zero'
function zero<T>(x: T | null): bigint {
  return 0n;
}
export function f(): bigint {
  return zero(null);
}
