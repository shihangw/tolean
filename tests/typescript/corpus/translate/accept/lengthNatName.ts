// A parameter named Nat would hide the Lean type that the length of an
// array is written with, so the output writes it from the root.
export function size(Nat: ReadonlyArray<bigint>): number {
  return Nat.length;
}
