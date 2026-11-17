export class ParseError extends Error {
  readonly line: number;
  readonly label: string;
  constructor(message: string, readonly code: bigint, line: number, label: string) {
    super(message);
    this.line = line;
    this.label = label;
  }
}
