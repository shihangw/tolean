/**
 * A string iterates by code point: `for … of`, a spread and a pattern each
 * visit one string for each code point, so a surrogate pair such as the one
 * of U+1F600 is one value, and a lone surrogate is a value of its own.
 */
export function countChars(s: string): bigint {
  let n = 0n;
  for (const c of s) {
    if (c !== " ") {
      n = n + 1n;
    }
  }
  return n;
}

export function chars(s: string): ReadonlyArray<string> {
  return [...s];
}

export function withEnd(s: string): ReadonlyArray<string> {
  return [...s, "!"];
}

export function first(s: string): string {
  const [c] = s;
  return c ?? "";
}

export function rest(s: string): ReadonlyArray<string> {
  const [, ...others] = s;
  return others;
}

export function emoji(): ReadonlyArray<string> {
  return [..."a😀b"];
}

export function reversed(s: string): string {
  let r = "";
  for (const c of s) {
    r = c + r;
  }
  return r;
}
