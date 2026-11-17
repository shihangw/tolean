// expect: 5:3 error field order must match parameter properties followed by separate declarations
class E extends Error {
  readonly a: number;
  readonly b: number;
  constructor(b: number, a: number) {
    super("bad");
    this.a = a;
    this.b = b;
  }
}
