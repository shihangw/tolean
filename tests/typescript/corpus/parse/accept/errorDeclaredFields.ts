export class ParseError extends Error {
  readonly line: number;
  readonly label: string;
  constructor(message: string, readonly code: bigint, label: string, line: number) {
    super(message);
    this.label = label;
    this.line = line;
  }
}
