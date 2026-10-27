// expect: 2:84 the type fixes the answer of this test with null
export function f(x: bigint | null): boolean { if (x === null) return true; return x === null || x > 0n; }
