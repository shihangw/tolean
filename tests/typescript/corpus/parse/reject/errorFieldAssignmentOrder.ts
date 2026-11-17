// expect: 7:5 assign error fields in declaration order
class E extends Error {
  readonly a: number;
  readonly b: number;
  constructor(a: number, b: number) {
    super("bad");
    this.b = b;
    this.a = a;
  }
}
