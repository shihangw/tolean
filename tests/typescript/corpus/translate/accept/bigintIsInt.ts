// As a Nat, `0 - 1` is 0 and this would be false in Lean, true in JS.
export function f(): boolean { return 0n - 1n < 0n; }
