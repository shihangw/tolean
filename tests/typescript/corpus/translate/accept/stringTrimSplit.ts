/**
 * `trim`, `trimStart` and `trimEnd` remove white space and line terminators,
 * among them U+00A0 and U+2028. `split` with a string separator gives the
 * pieces between its occurrences, and an empty separator splits a string into
 * its code units.
 */
export interface Line {
  readonly text: string;
}

export function clean(s: string): string {
  return s.trim();
}

export function left(s: string): string {
  return s.trimStart();
}

export function right(s: string): string {
  return s.trimEnd();
}

/** U+00A0 is a space separator and U+2028 a line terminator. */
export function noBreak(): string {
  return "  a  ".trim();
}

export function isBlank(line: Line): boolean {
  return line.text.trim() === "";
}

export function fields(row: string): ReadonlyArray<string> {
  return row.split(",");
}

/** An empty separator gives each code unit, so a surrogate pair gives two. */
export function units(s: string): ReadonlyArray<string> {
  return s.split("");
}

export function words(lines: ReadonlyArray<Line>): ReadonlyArray<string> {
  return lines.map((l) => l.text.trim());
}

export function countFields(row: string): bigint {
  let n = 0n;
  for (const f of row.split(";")) {
    if (f.trim() !== "") {
      n = n + 1n;
    }
  }
  return n;
}
