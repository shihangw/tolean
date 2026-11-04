// Strings that Lean reads as modifiers or keywords name constructors too,
// and source names may hide the classes that the output derives.
type Repr = bigint;
type DecidableEq = 'yes' | 'no';
type Mode = 'unsafe' | 'partial' | 'noncomputable' | 'open';

export function isUnsafe(m: Mode): boolean {
  return m === 'unsafe';
}

export function agreed(a: DecidableEq): boolean {
  return a === 'yes';
}

export function size(r: Repr): Repr {
  return r;
}
