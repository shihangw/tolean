// certify: required
class ParseError extends Error {
  constructor(readonly code: string) {
    super(code);
    this.name = "NotTheConstructor";
  }
}

export function identity(n: number): number {
  return n;
}
