// expect: 9:21 a class-typed function must return new for the declared class
class C {
  readonly value: bigint;
  constructor(value: bigint) { this.value = value; }
  get(): bigint { return this.value; }
}
function make(): C {
  try { throw new Error("caught"); }
  catch (ignored) { return { value: 7n }; }
}
export function f(): bigint { return make().get(); }
