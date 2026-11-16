// An unrelated project unit must not reuse data.ts's private generated name
// or add an otherwise absent dependency on it.
export function point(n: number): { readonly n: number } {
  return { n };
}
