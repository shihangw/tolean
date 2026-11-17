// certify: required
interface Box<T> { readonly value: T; }

export function identity<T>(value: Box<T>["value"]): T {
  return value;
}

export function bigIdentity(value: bigint): bigint {
  return identity(value);
}
