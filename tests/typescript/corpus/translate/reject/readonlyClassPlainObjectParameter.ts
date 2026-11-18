// expect: 7:1 source functions may not accept class-typed parameters
class C {
  readonly value: bigint;
  constructor(value: bigint) { this.value = value; }
  get(): bigint { return this.value; }
}
export function f(c: C): bigint { return c.get(); }
