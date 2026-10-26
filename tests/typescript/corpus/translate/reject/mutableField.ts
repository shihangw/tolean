// expect: 2:15 interface fields must be readonly, required and typed
interface P { x: bigint }
export function f(p: P): bigint { return p.x; }
