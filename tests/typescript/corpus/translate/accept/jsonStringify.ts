/**
 * `JSON.stringify(x)` becomes `JSString.json x`, a function that the model
 * declares but does not define, so a claim cannot depend on the text. Its
 * argument is a string, a number, a boolean or null, or an array, a tuple or a
 * nullable value of them, whose text the Lean value fixes.
 */
export type Level = 'low' | 'high';

export function quote(s: string): string {
  return JSON.stringify(s);
}

export function flags(xs: ReadonlyArray<boolean>): string {
  return "flags " + JSON.stringify(xs);
}

export function pair(p: readonly [string, number]): string {
  return JSON.stringify(p);
}

export function maybe(s: string | null): string {
  return JSON.stringify(s);
}

export function level(l: Level): string {
  return JSON.stringify(l);
}

export function sameText(a: ReadonlyArray<string>, b: ReadonlyArray<string>): boolean {
  return JSON.stringify(a) === JSON.stringify(b);
}
