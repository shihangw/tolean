// certify: required
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
