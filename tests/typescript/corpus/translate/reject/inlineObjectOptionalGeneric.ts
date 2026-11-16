// expect: 3:3 optional nullable types with unresolved type parameters are not supported
export type OptionalGeneric<T> = {
  value?: T | null;
};
