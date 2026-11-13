// expect: 9:23 'limit' can throw, so a call of it may not stand in a branch of ?:, after &&, || or ??, in the test or the update of a for loop
// JS evaluates the test before each run of the body, so the call cannot move out of it.
export function limit(n: number): number {
  if (n < 0) throw new Error("negative");
  return n;
}
export function f(n: number): bigint {
  let s = 0n;
  for (let i = 0; i < limit(n); i++) {
    s += 1n;
  }
  return s;
}
