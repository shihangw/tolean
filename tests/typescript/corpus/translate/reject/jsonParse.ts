// expect: 3:10 only JSON.stringify is supported
export function read(s: string): boolean {
  return JSON.parse(s);
}
