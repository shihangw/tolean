// A file whose only numbers are results of findIndex still gets the number
// type.
export function sameFirst(xs: ReadonlyArray<bigint>, ys: ReadonlyArray<bigint>): boolean {
  return xs.findIndex((x) => x > 0n) === ys.findIndex((y) => y > 0n);
}
