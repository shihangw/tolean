// A file whose only numbers are lengths of arrays still gets the number type.
export function sameLength(xs: ReadonlyArray<bigint>, ys: ReadonlyArray<string>): boolean {
  return xs.length === ys.length;
}
