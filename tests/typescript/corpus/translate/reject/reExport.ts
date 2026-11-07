// expect: 3:1 tolean does not translate a re-export
function f(n: bigint): bigint { return n; }
export { f } from "./other.ts";
