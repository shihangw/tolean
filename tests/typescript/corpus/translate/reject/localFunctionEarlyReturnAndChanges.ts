// expect: 6:5 a branch that does not always return may not return, break or continue
export function count(x: bigint): bigint {
  let total = 0n;
  function add(y: bigint): bigint {
    total += y;
    if (y < 0n) {
      return total;
    }
    total += 1n;
    return total;
  }
  const result = add(x);
  return result + total;
}
