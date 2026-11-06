// A member of a tagged union with an optional field: its certificate splits
// the field into its two cases, as it does for an interface.
export interface A {
  readonly kind: 'a';
  readonly x?: bigint;
}

export interface B {
  readonly kind: 'b';
  readonly x: bigint;
}

export type U = A | B;

export function viaSwitch(u: U): bigint {
  switch (u.kind) {
    case 'a':
      return u.x ?? 0n;
    case 'b':
      return u.x;
  }
}

export function viaIf(u: U): bigint {
  if (u.kind === 'a') {
    return u.x ?? 0n;
  }
  return u.x;
}
