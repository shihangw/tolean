export class ParseError extends Error {
  readonly line: number;
  readonly label: string;

  constructor(message: string, line: number, label: string) {
    super(message);
    this.line = line;
    this.label = label;
  }
}

export function check(line: number): number {
  if (line < 0) {
    throw new ParseError("negative line", line, "source");
  }
  return line;
}
