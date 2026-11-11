// expect: 3:19 name 'prefix' is reserved in Lean
// Lean reads `prefix` as a keyword, so the output could not name the parameter.
export function f(prefix: string): boolean {
  return prefix === "";
}
