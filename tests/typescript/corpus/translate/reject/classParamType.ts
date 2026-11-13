// expect: 3:39 a parameter of an error class must be a bigint, a number, a boolean or a string
// A field of an error holds a primitive value.
class Bad extends Error { constructor(readonly xs: ReadonlyArray<bigint>) { super("bad"); } }
export function f(n: bigint): bigint { return n; }
