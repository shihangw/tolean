// expect: 6:19 '__proto__: v' sets the prototype of the object, not a field
export interface P {
  readonly x: bigint;
}
export function f(p: P): P {
  return { x: 1n, __proto__: p };
}
