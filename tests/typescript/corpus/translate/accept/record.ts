export type Kind = 'apple' | 'pear' | 'plum';

// A Record over a literal union has one property for each string, so it
// becomes a structure with one field for each.
export type Counts = Record<Kind, bigint>;

export type Labels = Readonly<Record<Kind, string>>;

// A structure whose fields are numbers is generic over the number type.
export type Weights = Record<Kind, number>;

export function empty(): Counts {
  return { apple: 0n, pear: 0n, plum: 0n };
}

// An index with a key of the literal union reads the field that it names.
export function count(c: Counts, k: Kind): bigint {
  return c[k];
}

export function fruit(c: Counts): bigint {
  return c.apple + c['pear'];
}

export function add(c: Counts, k: Kind, n: bigint): Counts {
  return {
    apple: k === 'apple' ? c.apple + n : c.apple,
    pear: k === 'pear' ? c.pear + n : c.pear,
    plum: k === 'plum' ? c.plum + n : c.plum,
  };
}

export function total(c: Counts, kinds: ReadonlyArray<Kind>): bigint {
  let sum = 0n;
  for (const k of kinds) {
    sum += c[k];
  }
  return sum;
}

export function label(l: Labels, k: Kind): string {
  return l[k];
}

export function weight(w: Weights, k: Kind): number {
  return w[k];
}
