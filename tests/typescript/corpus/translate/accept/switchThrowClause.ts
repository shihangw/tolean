// A clause of a switch that changes locals may end in a throw, as it may
// end in a break: JS never runs past the throw into the next clause. The
// match then runs in the Except monad, and the statements after it take the
// state from the clause that did not throw.
export interface A { readonly kind: "a"; readonly n: bigint; }
export interface B { readonly kind: "b"; readonly n: bigint; }
export interface C { readonly kind: "c"; readonly n: bigint; }
export type U = A | B | C;

export function onlyThrow(u: U): bigint {
  let w = 0n;
  switch (u.kind) {
    case "a":
      w = u.n;
      break;
    case "b":
      throw new Error("no b");
    case "c":
      w = u.n * 3n;
      break;
  }
  return w;
}
