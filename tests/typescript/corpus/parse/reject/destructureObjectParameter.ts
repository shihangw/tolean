// expect: 3:19 destructuring is not supported in parameters; name the parameter and read its fields in the body
// Parameter binding needs its own object-pattern semantics.
export function f({ a }: { readonly a: number }): number { return a; }
