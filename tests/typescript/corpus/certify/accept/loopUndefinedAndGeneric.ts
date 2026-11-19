// certify: required
export function firstUndef(xs: ReadonlyArray<bigint | undefined>): boolean {
  for (const x of xs) {
    if (x === undefined) return true;
  }
  return false;
}

export function firstGenericNull<T>(xs: ReadonlyArray<bigint>, value: T | null): boolean {
  for (const x of xs) {
    if (value === null) return true;
  }
  return false;
}

export function countUndefined(xs: ReadonlyArray<bigint | undefined>): bigint {
  let n = 0n;
  for (const x of xs) {
    if (x === undefined) n += 1n;
  }
  return n;
}

export function sumDefined(xs: ReadonlyArray<bigint | undefined>): bigint {
  let n = 0n;
  for (const x of xs) n += x ?? 0n;
  return n;
}

export function countGenericNull<T>(xs: ReadonlyArray<bigint>, value: T | null): bigint {
  let n = 0n;
  for (const x of xs) {
    if (value === null) n += 1n;
  }
  return n;
}

export function sumGenericCapture<T>(xs: ReadonlyArray<bigint>, value: T | null): bigint {
  let n = 0n;
  for (const x of xs) n += x;
  return n;
}

export function twoLoops(
  xs: ReadonlyArray<bigint | undefined>,
  ys: ReadonlyArray<bigint>,
): bigint {
  let n = 0n;
  for (const x of xs) {
    if (x !== undefined) n += x;
  }
  for (const y of ys) n += y;
  return n;
}

export function twoGeneric<T>(
  xs: ReadonlyArray<bigint>,
  ys: ReadonlyArray<bigint>,
  value: T | null,
): bigint {
  let n = 0n;
  for (const x of xs) {
    if (value === null) n += x;
  }
  for (const y of ys) {
    if (value !== null) n += y;
  }
  return n;
}

export function threeLoops(
  xs: ReadonlyArray<bigint | undefined>,
  ys: ReadonlyArray<bigint>,
  zs: ReadonlyArray<bigint>,
): bigint {
  let n = 0n;
  for (const x of xs) {
    if (x !== undefined) n += x;
  }
  for (const y of ys) n += y;
  for (const z of zs) n += z;
  return n;
}

export function mixedLoops<T>(
  xs: ReadonlyArray<bigint | undefined>,
  ys: ReadonlyArray<bigint>,
  zs: ReadonlyArray<bigint>,
  value: T | null,
): bigint {
  let n = 0n;
  for (const x of xs) {
    if (x !== undefined) n += x;
  }
  for (const y of ys) {
    if (value === null) n += y;
  }
  for (const z of zs) n += z;
  return n;
}

export function indexOfUndef(xs: ReadonlyArray<bigint | undefined>): bigint {
  let i = 0n;
  for (const x of xs) {
    if (x === undefined) return i;
    i += 1n;
  }
  return -1n;
}

export function indexOfNull(xs: ReadonlyArray<bigint | null>): bigint {
  let i = 0n;
  for (const x of xs) {
    if (x === null) return i;
    i += 1n;
  }
  return -1n;
}

export function returnThenLoopPlain(
  xs: ReadonlyArray<bigint>,
  ys: ReadonlyArray<bigint>,
): bigint {
  for (const x of xs) {
    if (x === 0n) return 0n;
  }
  let n = 0n;
  for (const y of ys) n += y;
  return n;
}

export function returnThenSecondLoop(
  xs: ReadonlyArray<bigint>,
  ys: ReadonlyArray<bigint>,
): bigint {
  for (const x of xs) {
    if (x === 0n) return 0n;
  }
  let n = 0n;
  for (const y of ys) n += y;
  for (const z of ys) n += z;
  return n;
}

export function returnWithTwoLocals(xs: ReadonlyArray<bigint | undefined>): bigint {
  let i = 0n;
  let n = 0n;
  for (const x of xs) {
    if (x === undefined) return i + n;
    i += 1n;
    n += x;
  }
  return -1n;
}

export function returnThenLoop(
  xs: ReadonlyArray<bigint | undefined>,
  ys: ReadonlyArray<bigint>,
): bigint {
  for (const x of xs) {
    if (x === undefined) return 0n;
  }
  let n = 0n;
  for (const y of ys) n += y;
  return n;
}

export function returnThenTwoLoops(
  xs: ReadonlyArray<bigint | undefined>,
  ys: ReadonlyArray<bigint>,
): bigint {
  for (const x of xs) {
    if (x === undefined) return 0n;
  }
  let n = 0n;
  for (const y of ys) n += y;
  for (const z of ys) n += z;
  return n;
}

export function returnNullThenLoop(
  xs: ReadonlyArray<bigint | null>,
  ys: ReadonlyArray<bigint>,
): bigint {
  for (const x of xs) {
    if (x === null) return 0n;
  }
  let n = 0n;
  for (const y of ys) n += y;
  return n;
}

export function nestedLoops<T>(
  xs: ReadonlyArray<bigint | undefined>,
  ys: ReadonlyArray<bigint>,
  value: T | null,
): bigint {
  let n = 0n;
  for (const x of xs) {
    if (x !== undefined) {
      n += x;
      for (const y of ys) {
        if (value === null) n += y;
      }
    }
  }
  return n;
}

export function nestedLoopsPlain(
  xs: ReadonlyArray<bigint>,
  ys: ReadonlyArray<bigint>,
): bigint {
  let n = 0n;
  for (const x of xs) {
    n += x;
    for (const y of ys) n += y;
  }
  return n;
}
