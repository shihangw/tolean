// expect: 4:3 change what its bound reads
export function f(n: number): number {
  const xs: Array<number> = [];
  for (let i = 0; i < xs.length + n; i++) { xs.push(i); }
  return xs.length;
}
