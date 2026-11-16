// expect: 4:3 optional nullable types with unresolved type parameters are not supported
type Maybe<T> = T | null;
export interface Box<T> {
  readonly value?: Maybe<T>;
}
