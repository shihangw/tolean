// `throw new Error(message)` ends a function with an error, so the function
// returns `Except JSError T`. A call of such a function as the whole value of a
// `const`, a `let` or a `return` passes the error on.
export interface Shelf {
  readonly label: string;
  readonly count: bigint;
}

export function checked(n: bigint): bigint {
  if (n < 0n) throw new Error("a count may not be negative");
  return n;
}

export function take(shelf: Shelf, n: bigint): Shelf {
  const k = checked(n);
  if (k > shelf.count) {
    throw new Error(shelf.label);
  }
  return { label: shelf.label, count: shelf.count - k };
}

export function moveBoth(a: bigint, b: bigint): bigint {
  let first: bigint = checked(a);
  first += 1n;
  return checked(first + b);
}

export function firstOver(xs: ReadonlyArray<bigint>, limit: bigint): bigint {
  for (const x of xs) {
    if (x > limit) return x;
  }
  throw new Error("no count is over the limit");
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

export function items(p: Pack): bigint {
  switch (p.kind) {
    case "box":
      return p.items;
    case "crate":
      throw new Error("open the crate first");
  }
}
