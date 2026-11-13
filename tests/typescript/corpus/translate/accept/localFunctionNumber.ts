// A local function is the only code that uses the number model, so the file
// needs `N` for its body.
export function pick(s: string): bigint {
  function small(t: string): boolean {
    return t.length < 3;
  }
  const b = small(s);
  return b ? 1n : 2n;
}
