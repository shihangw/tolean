// expect: 5:3 optional nullable types with unresolved type parameters are not supported
type Maybe<T> = T | null;
type Optional<T> = T | undefined;
export interface Box<T> {
  readonly values: ReadonlyArray<Optional<Maybe<T>>>;
}
