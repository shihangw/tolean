// A `throw`, or a call of a function that can throw, may stand in a loop body
// or in a branch that changes locals. The output runs the loop or the branch
// in the `Except` monad, and `>>=` passes the error on.
export function checked(n: bigint): bigint {
  if (n < 0n) throw new Error("a count may not be negative");
  return n;
}

export function sum(xs: ReadonlyArray<bigint>): bigint {
  let s = 0n;
  for (const x of xs) {
    if (x < 0n) throw new Error("negative");
    s += x;
  }
  return s;
}

export function sumChecked(xs: ReadonlyArray<bigint>): bigint {
  let s = 0n;
  for (const x of xs) {
    const y = checked(x);
    s += y;
  }
  return s;
}

export function firstChecked(xs: ReadonlyArray<bigint>, limit: bigint): bigint {
  for (const x of xs) {
    if (x > limit) return checked(x);
  }
  return 0n;
}

export function clamp(n: bigint, limit: bigint): bigint {
  let r = n;
  if (n > limit) {
    r = limit;
  } else if (n < -limit) {
    throw new Error("too small");
  }
  return r;
}

export function stepped(n: bigint): bigint {
  let r = n;
  if (n > 10n) {
    const k = checked(n - 10n);
    r = k + 1n;
  }
  return r;
}

export function count(n: number, limit: number): number {
  let c = 0;
  for (let i = 0; i < n; i++) {
    if (c > limit) throw new Error("over the limit");
    c += 2;
  }
  return c;
}

export function untilZero(xs: ReadonlyArray<bigint>): bigint {
  let s = 0n;
  for (const x of xs) {
    if (x === 0n) break;
    if (x < 0n) throw new Error("negative");
    s += x;
  }
  return s;
}

export interface Box {
  readonly kind: "box";
  readonly items: bigint;
}

export interface Crate {
  readonly kind: "crate";
  readonly boxes: bigint;
}

export type Pack = Box | Crate;

export function weigh(p: Pack, limit: bigint): bigint {
  let w = 0n;
  switch (p.kind) {
    case "box":
      w = p.items;
      break;
    case "crate":
      if (p.boxes > limit) throw new Error("too heavy");
      w = p.boxes * 10n;
      break;
  }
  return w;
}
