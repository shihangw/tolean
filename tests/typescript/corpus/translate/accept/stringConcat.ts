/**
 * `+` with a string on either side joins the code units. ToString converts a
 * bigint to its decimal digits and a boolean to "true" or "false". `s += e`
 * on a string local joins in the same way.
 */
export interface Item {
  readonly name: string;
  readonly count: bigint;
  readonly done: boolean;
}

export function join(a: string, b: string): string {
  return a + b;
}

export function greet(name: string): string {
  return "héllo, " + name + " 😀";
}

export function label(item: Item): string {
  return item.name + ": " + item.count;
}

export function status(item: Item): string {
  return "done=" + item.done;
}

/** `+` is left-associative, so the bigints add first, then the string joins. */
export function sumFirst(a: bigint, b: bigint): string {
  return a + b + "!";
}

export function countFirst(n: bigint, unit: string): string {
  return n + unit;
}

export function flag(b: boolean, tail: string): string {
  return b + tail;
}

export function csv(names: ReadonlyArray<string>): string {
  let out = "";
  for (const n of names) {
    if (out !== "") {
      out += ",";
    }
    out += n;
  }
  return out;
}

export function counts(items: ReadonlyArray<Item>): string {
  let out = "";
  for (const i of items) {
    out += i.count;
    out += i.done;
  }
  return out;
}

export function tagged(names: ReadonlyArray<string>): ReadonlyArray<string> {
  return names.map((n) => "#" + n);
}
