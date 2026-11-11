// expect: 4:10 'slice' with a negative start and an end that is not negative is not supported
// The output would need the length of the array to read this slice.
export function f(xs: ReadonlyArray<bigint>): ReadonlyArray<bigint> {
  return xs.slice(-2, 3);
}
