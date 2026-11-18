// certify: required
class C {
  readonly value: bigint;
  constructor(value: bigint) { this.value = value; }
  get(): bigint { return this.value; }
}

export function f(value: bigint): bigint {
  const c: C = new C(value);
  const { value: field } = c;
  return field + c.get();
}
