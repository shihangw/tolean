export class ParseError extends Error {
  readonly line: number;
  constructor(message: string, line: number) {
    super(message);
    this.name = "ParseError";
    this.line = line;
  }
}

export class TaggedError extends Error {
  constructor(readonly code: string) {
    super(code);
    this.name = "NotTheConstructor";
  }
}

export function check(line: number): number {
  if (line < 0) throw new ParseError("negative line", line);
  if (line === 0) throw new TaggedError("zero");
  return line;
}
