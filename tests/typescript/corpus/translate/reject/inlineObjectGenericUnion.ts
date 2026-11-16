// expect: 2:1 a union of string literals, primitive types or interfaces, or a Record, may not have type parameters
export type Result<T> =
  | { readonly kind: 'ok'; readonly value: T }
  | { readonly kind: 'error'; readonly message: string };
