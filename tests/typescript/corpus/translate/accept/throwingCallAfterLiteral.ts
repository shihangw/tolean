// A literal whose parts are all literals stays in place before a call that
// can throw: it reads no local and runs no call, so moving it would change
// nothing, and in place it takes the type of its position.
export interface P { readonly a: bigint; readonly b?: bigint; }
export interface A { readonly kind: "a"; readonly n: bigint; }
export interface B { readonly kind: "b"; readonly n: bigint; }
export type U = A | B;

export function checked(n: bigint): bigint {
  if (n < 0n) throw new Error("neg");
  return n;
}
export function g(p: P, n: bigint): bigint {
  return p.a + n;
}
export function h(u: U, n: bigint): bigint {
  if (u.kind === "a") return u.n + n;
  return n;
}
export function sum(xs: ReadonlyArray<bigint>, n: bigint): bigint {
  let s = n;
  for (const x of xs) {
    s += x;
  }
  return s;
}
export function f(x: bigint): bigint {
  return g({ a: 1n }, checked(x)) + h({ kind: "a", n: 2n }, checked(x)) + sum([], checked(x));
}
export function negated(x: bigint): bigint {
  return g({ a: -1n }, checked(x)) + h({ kind: "a", n: -2n }, checked(x)) + sum([-1n], checked(x)) +
    g(({ a: 1n }), checked(x));
}
