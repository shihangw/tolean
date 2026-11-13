/**
 * `+` with a string and a number converts the number with ToString, which
 * becomes `JSNumber.toStr`. The model leaves it abstract, and
 * `SafeIntLaws.toStr` says that a safe integer gives its decimal digits.
 */
export interface Item {
  readonly name: string;
  readonly price: number;
}

export function label(i: Item): string {
  return i.name + ": " + i.price;
}

export function count(n: number): string {
  return n + " items";
}

export function log(xs: ReadonlyArray<number>): string {
  let s = "";
  for (const x of xs) {
    s += x;
    s += ",";
  }
  return s;
}
