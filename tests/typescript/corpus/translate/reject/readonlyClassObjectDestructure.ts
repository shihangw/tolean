// expect: 9:3 'get' is not a field
class C {
  readonly value: bigint;
  constructor(value: bigint) { this.value = value; }
  get(): bigint { return this.value; }
}

export function f(): bigint {
  const { get } = new C(7n);
  return get();
}
