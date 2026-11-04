// expect: 3:42 the value does not have the function's return type
type T = 'a' | 'b';
export function f(t: T): string { return t; }
