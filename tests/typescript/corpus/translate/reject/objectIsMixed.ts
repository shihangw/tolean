// expect: 2:59 Object.is needs two numbers, or two values of one primitive type
export function f(a: number, b: string): boolean { return Object.is(a, b); }
