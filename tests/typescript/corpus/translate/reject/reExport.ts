// expect: 3:1 './other.ts' is not a translated file of the project
function f(n: bigint): bigint { return n; }
export { f } from "./other.ts";
