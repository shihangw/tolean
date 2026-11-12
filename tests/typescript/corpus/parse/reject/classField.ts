// expect: 3:3 tolean supports only 'class Name extends Error'
class Bad extends Error {
  readonly id: string = "x";
}
