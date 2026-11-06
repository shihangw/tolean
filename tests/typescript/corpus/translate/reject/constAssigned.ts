// expect: 3:3 'x' is a const, and a later statement assigns it; declare it with let
export function f(): bigint | null {
  const x: bigint | null = null;
  x ??= 1n;
  return x;
}
