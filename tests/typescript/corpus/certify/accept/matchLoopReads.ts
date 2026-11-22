// certify: required
export function countNulls(xs: ReadonlyArray<bigint | null>): bigint {
  let n = 0n;
  for (const x of xs) {
    if (x === null) n += 1n;
  }
  return n;
}

export function capturedNull(xs: ReadonlyArray<bigint>, value: bigint | null): bigint {
  let n = 0n;
  for (const x of xs) {
    if (value === null) n += 1n;
  }
  return n;
}

type Choice = { kind: "left"; value: bigint } | { kind: "right"; value: bigint };

export function countLeft(xs: ReadonlyArray<Choice>): bigint {
  let n = 0n;
  for (const x of xs) {
    if (x.kind === "left") n += 1n;
  }
  return n;
}

export function capturedTag(xs: ReadonlyArray<bigint>, value: Choice): bigint {
  let n = 0n;
  for (const x of xs) {
    if (value.kind === "left") n += 1n;
  }
  return n;
}

export function independentCount<T>(xs: ReadonlyArray<T>): bigint {
  let n = 0n;
  for (const x of xs) n += 1n;
  return n;
}
