// `for (let i = k; i < b; i++)`, where `k` is an integer literal, runs over
// `JSNumber.countUp k b`: `k`, then each integer after it that is less than
// `b`. The update may also be `++i`
// or `i += 1`, and the body may `continue`, `break` or `return`, as in a
// `for … of` loop.
export function sumBelow(n: number): number {
  let total = 0;
  for (let i: number = 0; i < n; i++) {
    total = total + i;
  }
  return total;
}

export function sumAt(xs: ReadonlyArray<bigint>): bigint {
  let total = 0n;
  for (let i = 0; i < xs.length; ++i) {
    total = total + (xs[i] ?? 0n);
  }
  return total;
}

export function sumExcept(hi: number, skip: number): number {
  let total = 0;
  for (let i = -2; i < hi; i += 1) {
    if (i === skip) continue;
    total = total + i;
  }
  return total;
}

export function firstNegative(xs: ReadonlyArray<number>): number {
  for (let i = 0; i < xs.length; i++) {
    if ((xs[i] ?? 0) < 0) {
      return i;
    }
  }
  return -1;
}

export function prefixSum(xs: ReadonlyArray<bigint>, limit: bigint): bigint {
  let total = 0n;
  for (let i = 0; i < xs.length; i++) {
    const x = xs[i] ?? 0n;
    if (total + x > limit) break;
    total = total + x;
  }
  return total;
}
