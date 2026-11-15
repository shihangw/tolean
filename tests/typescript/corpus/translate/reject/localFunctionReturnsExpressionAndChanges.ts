// expect: 4:3 a state-writing local function must end by returning a captured variable
export function f(x: bigint): bigint {
  let total = 0n;
  function add(y: bigint): bigint {
    total += y;
    return total + 1n;
  }
  const result = add(x);
  return result + total;
}
