// expect: 4:3 error field order must match parameter properties followed by separate declarations
class E extends Error {
  readonly a: number;
  constructor(a: number, readonly b: number) {
    super("bad");
    this.a = a;
  }
}
