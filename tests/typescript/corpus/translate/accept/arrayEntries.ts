// `xs.entries()` gives each element with its index, as `[i, x]`. A loop, a
// spread and `new Map` use the iterator up at once, so the output reads it as
// the list `JSNumber.entries xs` of pairs.
export function firstTwoSum(xs: ReadonlyArray<bigint>): bigint {
  let total = 0n;
  for (const [i, x] of xs.entries()) {
    if (i < 2) {
      total = total + x;
    }
  }
  return total;
}

export function lastPlace(xs: ReadonlyArray<string>, s: string): number {
  let found = -1;
  for (const [i, x] of xs.entries()) {
    if (x === s) {
      found = i;
    }
  }
  return found;
}

export function indexSum(xs: ReadonlyArray<boolean>): number {
  let total = 0;
  for (const e of xs.entries()) {
    if (e[1]) {
      total = total + e[0];
    }
  }
  return total;
}

export function pairs(xs: ReadonlyArray<string>): ReadonlyArray<[number, string]> {
  return [...xs.entries()];
}

// Parentheses around the call change nothing.
export function parenSum(xs: ReadonlyArray<bigint>): bigint {
  let total = 0n;
  for (const [, x] of (xs.entries())) {
    total = total + x;
  }
  return total;
}
