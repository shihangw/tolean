class C {
  readonly value: bigint;
  constructor(value: bigint) { this.value = value; }
  get(): bigint { return this.value; }
}

export function f(): bigint | undefined {
  const m = new Map<string, bigint>();
  m.set("x", 7n);
  return m.get("x");
}
