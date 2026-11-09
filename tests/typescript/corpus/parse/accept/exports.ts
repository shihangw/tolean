function f(n: bigint): bigint { return n; }
interface G { readonly x: bigint; }
type H = bigint;
export { f, type G };
export type { H };
export {
  f,
} from "./b.ts"
