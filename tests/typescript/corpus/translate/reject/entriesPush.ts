// expect: 10:23 an owned array may be read only in the return value
// A JS iterator is live: a push inside the loop would add an element that
// the loop then visits. The output reads the entries once, when the loop
// starts. The two agree only because no accepted loop can change the array
// it runs over: an owned array may not be read in a loop head at all, and a
// parameter is a ReadonlyArray.
export function f(xs: ReadonlyArray<bigint>): bigint {
  const ys: Array<bigint> = [...xs];
  let total = 0n;
  for (const [, x] of ys.entries()) {
    ys.push(x);
    total = total + x;
  }
  return total;
}
