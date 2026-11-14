// expect: 4:3 a local function that returns a value may not change a variable
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
