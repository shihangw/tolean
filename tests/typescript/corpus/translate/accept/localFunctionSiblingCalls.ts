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

export function captured(factor: bigint, x: bigint): bigint {
  function scale(value: bigint): bigint {
    return value * factor;
  }
  function apply(value: bigint): bigint {
    const scaled = scale(value);
    return scaled + factor;
  }
  return apply(x);
}

export function siblingState(start: bigint, amount: bigint): bigint {
  let total = start;
  function add(value: bigint): void {
    total += value;
  }
  function twice(value: bigint): bigint {
    add(value);
    add(value);
    total += 1n;
    return total;
  }
  const result = twice(amount);
  return result + total;
}
