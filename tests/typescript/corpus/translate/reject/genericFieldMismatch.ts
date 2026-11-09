// expect: 6:12 'value' does not have the field's type
interface Box<T> {
  readonly value: T;
}
export function f(): Box<bigint> {
  return { value: 'a' };
}
