// expect: 3:15 an error field may not be named __proto__
class E extends Error {
  constructor(readonly __proto__: number) { super("bad"); }
}
export function check(): number { throw new E(7); }
