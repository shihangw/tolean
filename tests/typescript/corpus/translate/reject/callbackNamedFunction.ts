// expect: 6:10 an array method here takes one arrow function with one parameter
function positive(x: bigint): boolean {
  return x > 0n;
}
export function f(xs: ReadonlyArray<bigint>): ReadonlyArray<bigint> {
  return xs.filter(positive);
}
