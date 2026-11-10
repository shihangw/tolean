// expect: 4:10 'reduce' takes an arrow function with two parameters and an initial value
// Without an initial value, reduce throws on an empty array.
export function f(xs: ReadonlyArray<bigint>): bigint {
  return xs.reduce((a, x) => a + x);
}
