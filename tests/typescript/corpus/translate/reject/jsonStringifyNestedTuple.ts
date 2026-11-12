// expect: 5:25 JSON.stringify needs
// Lean writes [string, [string, string]] and [string, string, string] both as
// JSString × JSString × JSString, so the two would get the same text.
export function same(nested: readonly [string, readonly [string, string]]): string {
  return JSON.stringify(nested);
}
