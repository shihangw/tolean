// expect: 2:17 type parameters with a constraint are not supported
interface Box<T extends string> {
  readonly value: T;
}
