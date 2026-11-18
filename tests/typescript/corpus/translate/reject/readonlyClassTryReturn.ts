// expect: 8:9 a class-typed function must return new for the declared class
class C {
  readonly value: bigint;
  constructor(value: bigint) { this.value = value; }
  get(): bigint { return this.value; }
}
function make(): C {
  try { return { value: 7n }; }
  catch (ignored) { return new C(1n); }
}
export function f(): bigint { return make().get(); }
