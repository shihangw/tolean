// expect: 12:3 class-typed locals
class C {
  readonly value: bigint;
  constructor(value: bigint) { this.value = value; }
  get(): bigint { return this.value; }
}

type A = C;

export function f(): bigint {
  const c: A = new C(7n);
  const fake: C = { ...c };
  return fake.get();
}
