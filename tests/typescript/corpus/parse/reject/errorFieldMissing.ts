// expect: 5:5 each declared error field must be assigned exactly once after super(message)
class ParseError extends Error {
  readonly line: number;
  constructor(line: number) {
    super("bad");
  }
}
