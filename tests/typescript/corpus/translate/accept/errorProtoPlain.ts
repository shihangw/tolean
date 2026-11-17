class E extends Error {
  constructor(__proto__: number) { super("bad"); }
}
export function check(): number { throw new E(7); }
