// expect: 2:71 Number.isFinite needs a number operand (narrow a nullable value first)
export function f(x: number | null): boolean { return Number.isFinite(x); }
