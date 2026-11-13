import { checked } from "./a.ts";

// viaImport throws only through the imported function, which the hoisting
// does not follow, so a call of it may not stand inside a larger expression.
export function viaImport(n: bigint): bigint {
  const m = checked(n);
  return m * 2n;
}

export function user(n: bigint): bigint {
  return viaImport(n) + 1n;
}
