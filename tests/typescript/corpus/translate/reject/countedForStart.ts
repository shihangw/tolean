// expect: 4:16 the start of a counted loop must be an integer literal
export function sumFrom(a: number, b: number): number {
  let s = 0;
  for (let i = a; i < b; i++) {
    s = s + i;
  }
  return s;
}
