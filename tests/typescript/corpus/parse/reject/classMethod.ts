// expect: 3:3 tolean supports only 'class Name extends Error'
class Bad extends Error {
  describe(): string { return "bad"; }
}
