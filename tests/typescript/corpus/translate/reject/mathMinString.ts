// expect: 2:70 Math.min needs number operands
export function f(x: number, s: string): number { return Math.min(x, s); }
