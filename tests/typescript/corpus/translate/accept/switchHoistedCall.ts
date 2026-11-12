// A call of a function that can throw inside a larger expression in a
// clause of a switch: the hoisting puts `const r0' = checked(u.n)` into the
// clause, before the statement that read the call. The clause may hold that
// declaration without braces, because no other clause can read a hoisted
// name. The same in a switch that changes locals.
export interface A { readonly kind: "a"; readonly n: bigint; }
export interface B { readonly kind: "b"; readonly n: bigint; }
export type U = A | B;

export function checked(n: bigint): bigint {
  if (n < 0n) throw new Error("negative");
  return n;
}

export function returning(u: U): bigint {
  switch (u.kind) {
    case "a":
      return checked(u.n) * 2n;
    case "b":
      return u.n;
  }
}

export function changing(u: U): bigint {
  let w = 0n;
  switch (u.kind) {
    case "a":
      w = checked(u.n);
      break;
    case "b":
      w = u.n;
      break;
  }
  return w;
}
