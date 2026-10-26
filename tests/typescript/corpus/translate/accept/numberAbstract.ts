// Never Lean's Float: number operations go through the JSNumber class.
export function f(a: number, b: number | null): boolean { return b === null || a < b; }
