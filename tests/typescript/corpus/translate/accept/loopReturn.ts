// `return` in a `for…of` loop: the loop runs with `forIn`, and its state
// starts with the value to return, which ends the function.

// A search that changes no local.
export function firstOver(xs: ReadonlyArray<bigint>, limit: bigint): bigint {
  for (const x of xs) {
    if (x > limit) return x;
  }
  return -1n;
}

// A return, a break and a continue in one loop, which also changes locals.
export function scan(xs: ReadonlyArray<bigint>): bigint {
  let sum = 0n;
  let count = 0n;
  for (const x of xs) {
    if (x === 0n) continue;
    if (x < 0n) break;
    if (sum > 100n) {
      return sum * 10n;
    }
    sum += x;
    count += 1n;
  }
  return sum + count;
}

// The test of `null` narrows `x` for the rest of the body.
export function firstPresent(xs: ReadonlyArray<bigint | null>): bigint | null {
  for (const x of xs) {
    if (x !== null) return x;
  }
  return null;
}

// A loop in a branch that returns.
export function find(xs: ReadonlyArray<bigint>, on: boolean, target: bigint): boolean {
  if (on) {
    for (const x of xs) {
      if (x === target) return true;
    }
    return false;
  }
  return false;
}
