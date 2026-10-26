// After the guard, x is the value inside the Option, so x === null is false.
export function f(x: bigint | null): boolean { if (x === null) return true; return x === null || x > 0n; }
