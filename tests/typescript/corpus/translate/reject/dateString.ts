// expect: 2:54 new Date(v) needs a number
export function f(s: string): Date { return new Date(s); }
