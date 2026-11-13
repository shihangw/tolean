// expect: 4:5 tolean supports only 'class Name extends Error'
class Bad extends Error {
  constructor(readonly id: string) {
    this.id = id;
  }
}
