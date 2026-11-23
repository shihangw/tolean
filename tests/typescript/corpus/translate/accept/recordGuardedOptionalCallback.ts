// certify: required
export function missing(r: Record<string, number | undefined>, keys: string[]): boolean[] {
  return keys.map(k => Object.hasOwn(r, k) ? r[k] === undefined : true);
}
