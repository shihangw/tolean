// expect: 8:63 class constructors may not be shadowed
class C {
  readonly value: bigint;
  constructor(value: bigint) { this.value = value; }
  get(): bigint { return this.value; }
}
export function f(): bigint {
  try { throw new Error("caught"); } catch (C) { const fake = new C(7n); return fake.get(); }
}
