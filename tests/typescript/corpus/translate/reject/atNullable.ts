// expect: 3:10 'at' on an array of nullable values could give null or undefined
export function f(xs: ReadonlyArray<string | null>): string {
  return xs.at(-1) ?? '';
}
