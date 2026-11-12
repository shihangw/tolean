// expect: 5:5 tolean supports only 'class Name extends Error'
class Bad extends Error {
  constructor(readonly id: string) {
    super("bad");
    console.log(id);
  }
}
