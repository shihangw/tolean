// expect: 2:48 the global isNaN converts its argument to a number; use Number.isNaN
export function f(x: number): boolean { return isNaN(x); }
