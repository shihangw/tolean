// A function that owns an array may declare a local function, as long as
// the local function never names the array.
export function tagged(xs: ReadonlyArray<bigint>): bigint[] {
  const out: bigint[] = [];
  let n = 0n;
  function bump(k: bigint): void {
    n += k;
  }
  for (const x of xs) {
    bump(x);
    out.push(x + n);
  }
  return out;
}
