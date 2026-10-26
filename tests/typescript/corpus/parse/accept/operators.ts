export function operators(a: number, b: number, c: number | null): boolean {
  let x = a ** b ** 2;
  x = (-a) ** 2;
  x = --a ** 2;
  x **= 2;
  x >>>= 1;
  x >>= 1;
  x <<= 1;
  x = a >>> b >> 1 << 2;
  const n = c ?? c ?? 0;
  const m = (a > 0 || b > 0) ?? false;
  const s = typeof a === 'number' ? void 0 : a;
  x = a % b * c === null ? 1 : 2;
  return a >= b && b <= c || a instanceof Object || 'k' in s;
}
