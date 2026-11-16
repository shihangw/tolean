export function point(n: number): { readonly n: number } {
  return { n };
}

export function box<T>(value: T): { readonly value: T } {
  return { value };
}
