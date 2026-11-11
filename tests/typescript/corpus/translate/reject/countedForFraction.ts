// expect: 2:64 the start of a counted loop must be an integer literal
export function f(b: number): number { let s = 0; for (let i = 0.5; i < b; i++) { s = s + i; } return s; }
