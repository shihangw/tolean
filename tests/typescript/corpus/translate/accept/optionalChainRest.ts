// A read after `?.` is a part of the same optional chain: `p?.q.y` is
// `undefined` when `p` is null or undefined, and `p.q.y` otherwise.
export interface Leaf {
  readonly y: bigint;
  readonly label?: string;
}

export interface Mid {
  readonly leaf: Leaf;
  readonly next?: Leaf;
}

export interface Top {
  readonly mid: Mid;
  readonly z: bigint;
}

export function y(p: Mid | null): bigint {
  return p?.leaf.y ?? 0n;
}

export function deep(t: Top | null): bigint {
  return t?.mid.leaf.y ?? t?.z ?? 0n;
}

// The last field may be optional.
export function label(p: Mid | null): string {
  return p?.leaf.label ?? 'none';
}

export function missing(p: Mid | null): boolean {
  return p?.leaf.y === undefined;
}

// A `?.` after the chain starts another step of it.
export function nextY(p: Mid | null): bigint {
  return p?.leaf.label !== undefined ? 1n : p?.next?.y ?? 0n;
}

// The left side may be an optional field.
export interface Holder {
  readonly mid?: Mid;
}

export function heldY(h: Holder): bigint {
  return h.mid?.leaf.y ?? 0n;
}

export function sumY(ms: ReadonlyArray<Mid | null>): bigint {
  let n = 0n;
  for (const m of ms) {
    n += m?.leaf.y ?? 0n;
  }
  return n;
}
