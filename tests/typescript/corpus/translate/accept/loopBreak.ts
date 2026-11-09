// `break` in a `for…of` loop: the loop runs with `forIn`, and a `break` ends
// it with the locals as they are.

export function sumUntilNegative(xs: ReadonlyArray<bigint>): bigint {
  let s = 0n;
  for (const x of xs) {
    if (x < 0n) break;
    s += x;
  }
  return s;
}

// A `break` that ends a branch after it changes a local, and a `continue`.
export function firstOver(xs: ReadonlyArray<bigint>, limit: bigint): bigint {
  let found = -1n;
  let seen = 0n;
  for (const x of xs) {
    if (x === limit) continue;
    if (x > limit) {
      found = x;
      break;
    }
    seen += 1n;
  }
  return found * 1000n + seen;
}

// The test of `null` narrows `x` for the rest of the body.
export function sumPresent(xs: ReadonlyArray<bigint | null>): bigint {
  let s = 0n;
  for (const x of xs) {
    if (x === null) {
      break;
    }
    s += x;
  }
  return s;
}

// A `break` of an inner loop ends only that loop.
export function countPairs(xs: ReadonlyArray<bigint>, ys: ReadonlyArray<bigint>): bigint {
  let n = 0n;
  for (const x of xs) {
    for (const y of ys) {
      if (y > x) break;
      n += 1n;
    }
  }
  return n;
}
