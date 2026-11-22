class C {
  readonly value: bigint;
  constructor(value: bigint) { this.value = value; }
  get(): bigint { return this.value; }
}
function make(): C {
  try { throw new Error("caught"); }
  catch (ignored) { return new C(7n); }
}
export function f(): bigint { return make().get(); }
export function localCatch(): bigint {
  try { throw new Error("caught"); }
  catch (ignored) {
    const c: C = new C(11n);
    return c.get();
  }
}
export function untouched(): bigint {
  const c = new C(13n);
  try { return 17n; }
  catch (c) { return 19n; }
}
