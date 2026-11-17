// expect: 8:22 a class-typed function must return new for the declared class
class C {
  readonly value: bigint;
  constructor(value: bigint) { this.value = value; }
  get(): bigint { return this.value; }
}
type A = C;
function make(): A { return { value: 7n }; }
export function f(): bigint {
  const c: A = make();
  return c.get();
}
