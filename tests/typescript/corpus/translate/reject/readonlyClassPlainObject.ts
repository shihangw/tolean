// expect: 9:3 class-typed locals
class C {
  readonly value: bigint;
  constructor(value: bigint) { this.value = value; }
  get(): bigint { return this.value; }
}

export function f(): bigint {
  const c: C = { value: 7n };
  return c.get();
}
