// expect: 3:3 destructuring an array of nullable values could give null or undefined
export function f(xs: ReadonlyArray<bigint | null>): bigint {
  const [a] = xs;
  return a ?? 0n;
}
