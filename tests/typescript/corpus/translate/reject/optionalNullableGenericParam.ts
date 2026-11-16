// expect: 2:22 optional nullable types with unresolved type parameters are not supported
export function f<T>(value?: T | null): boolean {
  return value === null;
}
