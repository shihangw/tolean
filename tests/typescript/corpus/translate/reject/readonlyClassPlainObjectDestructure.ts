// expect: 9:3 class-typed destructuring bindings are not supported
class C {
  readonly value: bigint;
  constructor(value: bigint) { this.value = value; }
  get(): bigint { return this.value; }
}

export function f(): bigint {
  const { child }: { child: C } = { child: new C(7n) };
  return child.get();
}
