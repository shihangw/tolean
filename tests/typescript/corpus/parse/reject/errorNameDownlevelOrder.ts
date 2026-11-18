// expect: 7:5 before ES2022, assign this.name after the declared fields
// target: ES2015
class E extends Error {
  readonly line: number;
  constructor(line: number) {
    super("bad");
    this.name = "E";
    this.line = line;
  }
}
