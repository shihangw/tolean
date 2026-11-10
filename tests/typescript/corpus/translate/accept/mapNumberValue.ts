// A number that only the type arguments of `new Map` name.
export function f(): boolean {
  const m = new Map<bigint, number>();
  return m.has(1n);
}
