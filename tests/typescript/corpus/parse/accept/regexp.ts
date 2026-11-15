export function regexSyntax(s: string, a: number, b: number): boolean {
  const letters = /(?:^[a-z]+$)/;
  const captures = /(?:(a|ab)(?:c)?)/;
  const ranges = /(?:[^\d\w\s/]+)/;
  const slash = /(?:[/]\/)/;
  const escape = /(?:\uD800[\x20-\x7e])/;
  const unicode = /(?:😀|.)/;
  const counts = /(?:a{2}b{1,}c{0,3})/;
  const emptyClass = /(?:[]|[^])/;
  if (s.length === 0) return /(?:)/.test(s);
  if (a > b) /(?:a)/.test(s);
  return letters.test(s) || captures.test(s) || ranges.test(s)
    || slash.test(s) || escape.test(s) || unicode.test(s)
    || counts.test(s) || emptyClass.test(s) || a/b > a/(b + 1);
}
