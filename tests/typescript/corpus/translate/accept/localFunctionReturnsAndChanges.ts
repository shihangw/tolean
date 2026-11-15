// A final return reads a variable from the captured state.
export function f(x: bigint): bigint {
  let n = 0n;
  function bump(): bigint {
    n += 1n;
    return n;
  }
  const y = bump();
  return x + y;
}

export function tally(start: bigint, amount: bigint): bigint {
  let total = start;
  let count = 0n;
  const add = (x: bigint): bigint => {
    total += x;
    count += 1n;
    return total;
  };
  const first = add(amount);
  let second = add(-amount);
  second += count;
  return first + second + total + count;
}

export function returnCall(start: bigint, amount: bigint): bigint {
  let total = start;
  function add(x: bigint): bigint {
    total += x;
    return total;
  }
  return add(amount);
}

export function loopCalls(xs: ReadonlyArray<bigint>): bigint {
  let total = 0n;
  let result = 0n;
  function add(x: bigint): bigint {
    total += x;
    return total;
  }
  for (const x of xs) {
    const value = add(x);
    result += value;
  }
  return result + total;
}
