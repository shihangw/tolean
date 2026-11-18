export class ParseError extends Error {
  readonly line: number;
  constructor(message: string, line: number) {
    super(message);
    this.name = "ParseError";
    this.line = line;
  }
}
class DifferentError extends Error {
  constructor(readonly code: string) {
    super(code);
    this.name = "";
  }
}
