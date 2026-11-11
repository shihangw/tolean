// expect: 3:10 a string has no property 'size' here, only 'length'
export function f(s: string): number {
  return s.size;
}
