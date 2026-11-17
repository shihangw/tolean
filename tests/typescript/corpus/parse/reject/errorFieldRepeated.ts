// expect: 7:5 an error assignment must target an unassigned declared readonly field
class ParseError extends Error {
  readonly line: number;
  constructor(line: number) {
    super("bad");
    this.line = line;
    this.line = line;
  }
}
