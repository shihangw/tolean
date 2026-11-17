// expect: cannot encode the result of check
class ParseError extends Error {
  readonly line: number;
  constructor(line: number) {
    super("negative line");
    this.line = line;
  }
}

export function check(line: number): number {
  if (line < 0) throw new ParseError(line);
  return line;
}
