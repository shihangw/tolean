// expect: 3:10 'find' on an array of nullable values could give null or undefined
export function f(xs: ReadonlyArray<bigint | null>): bigint {
  return xs.find(x => x === null) ?? 0n;
}
