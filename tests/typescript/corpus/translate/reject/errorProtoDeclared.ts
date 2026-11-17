// expect: 4:15 an error field may not be named __proto__
class E extends Error {
  readonly __proto__: number;
  constructor(__proto__: number) { super("bad"); this.__proto__ = __proto__; }
}
export function check(): number { throw new E(7); }
