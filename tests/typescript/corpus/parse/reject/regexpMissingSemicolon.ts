// expect: 4:3 a semicolon is required before a regular expression statement
export function f(s: string): boolean {
  const n = 1
  /(?:a)/.test(s);
  return n === 1;
}
