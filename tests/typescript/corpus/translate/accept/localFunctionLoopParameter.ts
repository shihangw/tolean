// A parameter does not become a closure when a later local has its name.
export function tally(xs: ReadonlyArray<bigint>): bigint {
  function sum(scale: bigint): bigint {
    let total = 0n;
    for (const x of xs) {
      total += scale * x;
    }
    return total;
  }
  function scale(value: bigint): bigint {
    return value;
  }
  return sum(2n);
}
