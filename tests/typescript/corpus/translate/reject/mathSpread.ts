// expect: 2:59 a spread '...' may only be an element of an array literal
export function f(xs: number[]): number { return Math.max(...xs); }
