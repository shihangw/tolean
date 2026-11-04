// expect: 3:54 === needs two values of the same primitive type
type T = 'a' | 'b';
export function f(t: T, s: string): boolean { return t === s; }
