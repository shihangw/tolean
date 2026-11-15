export function JSRegExp(s: string): boolean {
  return /(?:\d{2,4})/.test(s);
}
