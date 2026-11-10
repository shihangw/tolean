// expect: 6:5 a call of a function that can throw may stand only in the statements that end the function
function check(n: bigint): bigint { if (n < 0n) throw new Error("negative"); return n; }
export function f(xs: ReadonlyArray<bigint>): bigint {
  let s = 0n;
  for (const x of xs) {
    const y = check(x);
    s += y;
  }
  return s;
}
