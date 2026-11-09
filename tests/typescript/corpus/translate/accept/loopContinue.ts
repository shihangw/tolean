// `continue` in a `for…of` loop: the rest of the body is the other branch of
// the `if` that continues.

export function sumPositive(xs: ReadonlyArray<bigint>): bigint {
  let s = 0n;
  for (const x of xs) {
    if (x <= 0n) continue;
    s += x;
  }
  return s;
}

// The test narrows `x` for the rest of the body, as after a return.
export function sumPresent(xs: ReadonlyArray<bigint | null>): bigint {
  let s = 0n;
  for (const x of xs) {
    if (x === null) {
      continue;
    }
    s += x;
  }
  return s;
}

// A branch that changes a local before it continues, and an else.
export function split(xs: ReadonlyArray<bigint>, limit: bigint): bigint {
  let small = 0n;
  let large = 0n;
  for (const x of xs) {
    if (x > limit) {
      const over = x - limit;
      large += over;
      continue;
    } else {
      small += x;
    }
  }
  return small * 1000n + large;
}

// A loop whose body continues, in a branch of an if.
export function evens(xs: ReadonlyArray<bigint>, on: boolean): bigint {
  let n = 0n;
  if (on) {
    for (const x of xs) {
      if (x % 2n !== 0n) continue;
      n += 1n;
    }
  }
  return n;
}
