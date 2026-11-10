// expect: 5:5 a branch that does not always return may not return, throw
export function f(xs: ReadonlyArray<bigint>): bigint {
  let s = 0n;
  for (const x of xs) {
    if (x < 0n) throw new Error("negative");
    s += x;
  }
  return s;
}
