// expect: 5:22 'Box' takes 1 type argument
interface Box<T> {
  readonly value: T;
}
export function f(b: Box): bigint {
  return 0n;
}
