// certify: required
interface JSNumber { readonly value: bigint; }
interface SafeIntLaws { readonly value: bigint; }
interface Eval { readonly value: bigint; }
export function f(xs: ReadonlyArray<bigint>, Int: bigint, compareOn: bigint): bigint[] {
  return xs.toSorted((a, b) => 0);
}
