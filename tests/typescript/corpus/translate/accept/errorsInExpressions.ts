// A call of a function that can throw may stand inside a larger expression.
// The output binds it with `>>=` before the statement, after every operand
// that JS evaluates before the call, and the statement reads the bound names.
export interface Shelf {
  readonly label: string;
  readonly count: bigint;
}

export function checked(n: bigint): bigint {
  if (n < 0n) throw new Error("a count may not be negative");
  return n;
}

export function plusOne(n: bigint): bigint {
  return checked(n) + 1n;
}

export function total(shelf: Shelf, n: bigint): bigint {
  return shelf.count * 2n + checked(n);
}

export function both(a: bigint, b: bigint): bigint {
  const s = checked(a) + checked(b);
  return s;
}

export function nested(a: bigint): bigint {
  return checked(checked(a) - 1n);
}

export function over(a: bigint): boolean {
  if (checked(a) > 3n) {
    return true;
  }
  return false;
}

export function accumulate(xs: ReadonlyArray<bigint>): bigint {
  let s = 0n;
  for (const x of xs) {
    s += checked(x);
  }
  return s;
}

export function double(n: bigint): bigint {
  return n * 2n;
}

export function mixed(n: bigint): bigint {
  return double(n) + checked(n) + double(n);
}

export function labeled(shelf: Shelf, n: bigint): Shelf {
  return { label: shelf.label, count: checked(n) + shelf.count };
}

export function pushed(xs: ReadonlyArray<bigint>, n: bigint): ReadonlyArray<bigint> {
  const out: Array<bigint> = [];
  for (const x of xs) {
    out.push(checked(x) + n);
  }
  return out;
}
