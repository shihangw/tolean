/**
 * `<`, `<=`, `>` and `>=` on strings compare their UTF-16 code units, as
 * IsLessThan does. They become `JSString.lt` and `JSString.le`, and `>` and
 * `>=` swap the operands.
 */
export interface Entry {
  readonly key: string;
  readonly rank: bigint;
}

export function before(a: string, b: string): boolean {
  return a < b;
}

export function notAfter(a: string, b: string): boolean {
  return a <= b;
}

export function after(a: string, b: string): boolean {
  return a > b;
}

export function notBefore(a: string, b: string): boolean {
  return a >= b;
}

/** U+FFFF is one code unit, FFFF. '😀' starts with the code unit D83D, so it
 * is less, though its code point is greater. */
export function unitOrder(): boolean {
  return "😀" < "￿";
}

export function isEmpty(s: string): boolean {
  return s <= "";
}

export function earlier(a: Entry, b: Entry): Entry {
  return a.key < b.key ? a : b;
}

export function inRange(s: string, low: string, high: string): boolean {
  return low <= s && s < high;
}

export function smallest(keys: ReadonlyArray<string>, start: string): string {
  let min = start;
  for (const k of keys) {
    if (k < min) {
      min = k;
    }
  }
  return min;
}

export function atLeast(keys: ReadonlyArray<string>, low: string): ReadonlyArray<string> {
  return keys.filter((k) => k >= low);
}
