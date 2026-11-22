// certify: required
export function counts(r: Record<string, number>, keys: string[]): number[] {
  return keys.map(k => Object.hasOwn(r, k) ? (r[k] ?? 0) : 0);
}
