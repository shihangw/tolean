// expect: 3:10 'sort' changes the array that it sorts
export function f(xs: bigint[]): bigint[] {
  return xs.sort((a, b) => (a < b) ? -1 : (a > b) ? 1 : 0);
}
