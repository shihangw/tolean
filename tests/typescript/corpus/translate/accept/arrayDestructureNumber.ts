// A pattern whose value is a number makes the file generic over the number
// type, as a declaration of one does.
export function size(xs: ReadonlyArray<bigint>): bigint {
  const [n] = [xs.length];
  return n === undefined ? 0n : 1n;
}
