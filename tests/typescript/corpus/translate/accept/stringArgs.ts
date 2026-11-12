/**
 * The string methods with number arguments, each an integer literal: `at`
 * and `slice`, where a negative index counts from the end, `padStart` and
 * `padEnd`, the position of `startsWith`, `endsWith`, `includes` and
 * `indexOf`, and the limit of `split`. Each counts code units.
 */
export interface Row {
  readonly id: string;
  readonly text: string;
}

export function last(s: string): string {
  return s.at(-1) ?? "";
}

export function firstOr(s: string): string {
  return s.at(0) ?? "";
}

export function tail(s: string): string {
  return s.slice(1);
}

export function middle(s: string): string {
  return s.slice(1, -1);
}

export function whole(s: string): string {
  return s.slice();
}

export function lastThree(s: string): string {
  return s.slice(-3);
}

export function padId(r: Row): string {
  return r.id.padStart(6, "0");
}

export function column(s: string): string {
  return s.padEnd(10);
}

export function hasSuffixAt(s: string): boolean {
  return s.endsWith("b", 3);
}

export function prefixAfter(s: string): boolean {
  return s.startsWith("ab", 2);
}

export function containsLater(s: string): boolean {
  return s.includes("x", 4);
}

export function nextComma(s: string): number {
  return s.indexOf(",", 1);
}

export function firstTwo(s: string): ReadonlyArray<string> {
  return s.split(",", 2);
}

export function noPieces(s: string): ReadonlyArray<string> {
  return s.split(",", 0);
}

export function key(r: Row): string {
  return r.text.slice(0, 3).padEnd(3, "-");
}
