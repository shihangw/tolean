// expect: 2:73 === here would compare objects or nullable values; only primitives and null tests are supported
export function f(a: number | null, b: number | null): boolean { return a === b; }
