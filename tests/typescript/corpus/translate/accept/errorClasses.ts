// An error class, `class C extends Error`, becomes a constructor of the
// file's `Thrown`, with the message and the `readonly` parameters of its
// constructor as fields. `throw new C(args)` throws it, and `throw new
// Error(m)` throws `Thrown.error`. Every function that can throw returns
// `Except Thrown R`.
export class NotFound extends Error {}

export class TooMany extends Error {
  constructor(readonly limit: bigint, extra: string) {
    super("too many: " + extra);
  }
}

class Odd extends Error {
  constructor(readonly value: bigint, readonly label: string) {
    super(label);
  }
}

export function checked(n: bigint, limit: bigint): bigint {
  if (n < 0n) throw new NotFound("no count");
  if (n > limit) throw new TooMany(limit, "over");
  if (n === 7n) throw new Error("seven");
  return n;
}

export function twice(n: bigint, limit: bigint): bigint {
  return checked(n, limit) * 2n;
}

export function evens(xs: ReadonlyArray<bigint>): bigint {
  let s = 0n;
  for (const x of xs) {
    if (x % 2n === 1n) throw new Odd(x, "odd: " + "x");
    s += x;
  }
  return s;
}

export function described(n: bigint, extra: string): bigint {
  if (n > 100n) {
    throw new TooMany(n - 100n, extra);
  }
  return n;
}
