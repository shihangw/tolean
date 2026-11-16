// expect: 7:3 a value-returning sibling caller must write a captured variable directly
export function f(x: bigint): bigint {
  let total = 0n;
  function add(value: bigint): void {
    total += value;
  }
  function apply(value: bigint): bigint {
    add(value);
    return total;
  }
  const result = apply(x);
  return result + total;
}
