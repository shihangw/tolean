// The earlier sibling has no captures. Its caller can capture and change data.
export function calculate(x: bigint): bigint {
  function twice(value: bigint): bigint {
    return value * 2n;
  }
  function addOne(value: bigint): bigint {
    const doubled = twice(value);
    return doubled + 1n;
  }
  return addOne(x);
}

export function accumulate(xs: ReadonlyArray<bigint>): bigint {
  let total = 0n;
  function twice(value: bigint): bigint {
    return value * 2n;
  }
  const add = (value: bigint): bigint => {
    const doubled = twice(value);
    total += doubled;
    return total;
  };
  let seen = 0n;
  for (const x of xs) {
    const value = add(x);
    seen += value;
  }
  return total + seen;
}
