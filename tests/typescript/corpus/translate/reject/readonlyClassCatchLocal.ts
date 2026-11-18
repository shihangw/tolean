// expect: 9:5 class-typed locals must be initialized directly with new
class C {
  readonly value: bigint;
  constructor(value: bigint) { this.value = value; }
  get(): bigint { return this.value; }
}
export function f(): bigint {
  try { throw new Error("caught"); } catch (ignored) {
    const c: C = { value: 7n };
    return c.get();
  }
}
