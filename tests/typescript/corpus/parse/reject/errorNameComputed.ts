// expect: 5:17 this.name must be assigned a string literal
class E extends Error {
  constructor(label: string) {
    super(label);
    this.name = label;
  }
}
