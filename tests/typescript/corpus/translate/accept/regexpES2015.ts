// target: ES2015
export function whitespace(s: string): boolean {
  return /(?:^\s+$)/.test(s);
}
