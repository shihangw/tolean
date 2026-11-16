// expect: 5:34 a type may not include both null and undefined
type Maybe<T> = T | null;
type Optional<T> = T | undefined;
export interface Box<T> {
  readonly values: ReadonlyArray<Optional<Maybe<T>>>;
}
