// expect: 2:45 new Date takes no type arguments
export function f(t: number): Date { return new Date<number>(t); }
