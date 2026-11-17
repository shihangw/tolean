// expect: 9:3 destructuring class instances is not supported
class C {
  readonly value: bigint;
  constructor(value: bigint) { this.value = value; }
  get(): bigint { return this.value; }
}

export function f(): bigint {
  const { value } = new C(7n);
  return value;
}
