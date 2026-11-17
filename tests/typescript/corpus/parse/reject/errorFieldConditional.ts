// expect: 6:5 after super(message), error fields require unconditional
class ParseError extends Error {
  readonly line: number;
  constructor(line: number) {
    super("bad");
    if (line > 0) this.line = line;
  }
}
