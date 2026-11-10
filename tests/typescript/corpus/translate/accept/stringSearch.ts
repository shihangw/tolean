/**
 * `length`, `startsWith`, `endsWith`, `includes` and `indexOf` on strings
 * read the UTF-16 code units. So "😀".length is 2, and an index counts code
 * units too.
 */
export interface Entry {
  readonly key: string;
  readonly path: string;
}

export function size(s: string): number {
  return s.length;
}

export function isEmpty(s: string): boolean {
  return s.length === 0;
}

/** "😀" is a surrogate pair, two code units. */
export function emojiLength(): number {
  return "😀".length;
}

export function isPrivate(e: Entry): boolean {
  return e.key.startsWith("_");
}

export function isScript(e: Entry): boolean {
  return e.path.endsWith(".ts") || e.path.endsWith(".js");
}

export function mentions(text: string, name: string): boolean {
  return text.includes(name);
}

export function position(text: string, word: string): number {
  return text.indexOf(word);
}

export function inside(e: Entry): boolean {
  return e.path.indexOf("/") >= 0 && !e.path.startsWith("/");
}

export function matching(entries: ReadonlyArray<Entry>, start: string): ReadonlyArray<Entry> {
  return entries.filter((e) => e.key.startsWith(start));
}

export function countWith(names: ReadonlyArray<string>, part: string): bigint {
  let n = 0n;
  for (const name of names) {
    if (name.includes(part)) {
      n = n + 1n;
    }
  }
  return n;
}
