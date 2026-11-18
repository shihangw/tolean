// expect: 8:23 a class-typed function must return new for the declared class
class C {
  readonly value: bigint;
  constructor(value: bigint) { this.value = value; }
  get(): bigint { return this.value; }
  copy(): C {
    try { throw new Error("caught"); }
    catch (ignored) { return { value: 7n }; }
  }
}
export function f(): bigint { return new C(1n).copy().get(); }
