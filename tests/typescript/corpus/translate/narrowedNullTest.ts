export function f(x: bigint | null): boolean { if (x === null) return true; return x === null || x > 0n; }
