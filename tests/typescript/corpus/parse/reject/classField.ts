// expect: 3:23 default values are not supported
class Bad extends Error {
  readonly id: string = "x";
}
