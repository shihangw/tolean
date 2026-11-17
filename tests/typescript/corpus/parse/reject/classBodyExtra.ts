// expect: 5:5 after super(message), error fields require unconditional
class Bad extends Error {
  constructor(readonly id: string) {
    super("bad");
    console.log(id);
  }
}
