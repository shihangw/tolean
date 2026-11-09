interface Circle {
  readonly kind: 'circle';
  readonly r: bigint;
}

interface Square {
  readonly kind: 'square';
  readonly side: bigint;
}

export type Shape = Circle | Square;

export type Kind = 'circle' | 'square';

// Type stripping removes `as const` and `satisfies T`, so each has the value of
// the expression before it.
export function unit(): Shape {
  return { kind: 'circle', r: 1n } as const;
}

export function square(side: bigint): Shape {
  return { kind: 'square', side } satisfies Shape;
}

export function squareKind(): Kind {
  return 'square' as const;
}

export function sizes(): ReadonlyArray<bigint> {
  const xs: ReadonlyArray<bigint> = [1n, 2n] as const;
  return xs;
}

export function total(a: bigint, b: bigint): bigint {
  const t = a + b satisfies bigint;
  return t;
}

export function bigger(a: bigint, b: bigint): boolean {
  return a as const > b;
}

export type Value = string | bigint;

// A value keeps its own type after `satisfies`, even where the type that it
// names is a union that holds it.
export function name(s: string): string {
  return s satisfies Value;
}

// Where the context expects the union, the value becomes its member there.
export function wrap(s: string): Value {
  return s satisfies Value;
}

// Parentheses and `as const` keep the type of the value too.
export function nameInParens(s: string): string {
  return ((s)) satisfies Value;
}

export function nameAsConst(s: string): string {
  return s as const satisfies Value;
}

export function wrapInParens(s: string): Value {
  return (s satisfies Value);
}
