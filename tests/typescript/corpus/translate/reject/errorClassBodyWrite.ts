// expect: 5:5 an error assignment must target an unassigned declared readonly field
class Bad extends Error {
  constructor(readonly id: string) {
    super("bad");
    this.id = id;
  }
}
