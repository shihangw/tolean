export class ParseError extends Error {
  readonly line: number;
  readonly label: string;

  constructor(message: string, line: number, label: string) {
    super(message);
    this.label = label;
    this.line = line;
  }
}

export function check(line: number): number {
  if (line < 0) {
    throw new ParseError("negative line", line, "source");
  }
  return line;
}
