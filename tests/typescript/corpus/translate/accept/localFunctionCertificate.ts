// Certificates cover a local call that returns a value or writes back state.
export function tally(start: bigint, amount: bigint): bigint {
  let total = start;
  let count = 0n;
  function add(x: bigint): void {
    total += x;
    count += 1n;
  }
  const read = (scale: bigint): bigint => {
    return total * scale + count;
  };
  add(amount);
  const first = read(2n);
  add(-amount);
  return read(first);
}

export function twice(xs: ReadonlyArray<bigint>): ReadonlyArray<bigint> {
  function apply(ys: ReadonlyArray<bigint>): ReadonlyArray<bigint> {
    return ys.map(y => y * 2n);
  }
  return apply(xs);
}
