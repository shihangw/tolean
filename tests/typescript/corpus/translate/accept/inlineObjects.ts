export function id(x: { readonly n: bigint }): { readonly n: bigint } {
  return x;
}

export function make(n: bigint): { readonly n: bigint } {
  return { n };
}

export function use(n: bigint): bigint {
  return id(make(n)).n;
}

export function reordered(
  x: { readonly a: bigint; readonly b: boolean },
): { readonly b: boolean, readonly a: bigint } {
  return x;
}

export type Count = bigint;

export function aliases(x: { n: Count }): { readonly n: bigint } {
  return x;
}

export function generic<T>(x: { readonly value: T }): { readonly value: T } {
  return x;
}

export function alpha<U>(x: { readonly value: U }): { readonly value: U } {
  return generic(x);
}

export function concrete(value: bigint): bigint {
  const box: { readonly value: bigint } = { value };
  return generic(box).value;
}

export type Cell<T> = { readonly value: T };

export function typedCell<T>(x: Cell<T>): { readonly value: T } {
  return x;
}

export function unusedGeneric<A, B>(
  x: { readonly a: A },
  y: B,
): { readonly a: A } {
  return x;
}

export function nested(
  x: { readonly child: { readonly n: bigint }; readonly items: ReadonlyArray<{ readonly n: bigint }> },
): bigint {
  let result: bigint = x.child.n;
  for (const item of x.items) {
    result += item.n;
  }
  return result;
}

export function optional(x: { readonly n?: bigint | null }): bigint {
  return x.n ?? 0n;
}

export function satisfies(n: bigint): bigint {
  const value = { n } satisfies { readonly n: bigint };
  return value.n;
}

export function localValue(n: bigint): bigint {
  const value: { readonly n: bigint } = { n };
  return value.n;
}

export function arrayValue(n: bigint): ReadonlyArray<{ readonly n: bigint }> {
  return [{ n }];
}

// These source bindings must not collide with generated declarations or
// with the type parameters of generated structures.
export interface ToleanInline1 {
  readonly n: bigint;
}

export function names(x: { readonly ToleanInlineType1: bigint }): bigint {
  const ToleanInline2 = x.ToleanInlineType1;
  return ToleanInline2;
}
