// certify: required
export interface Span {
  readonly start: number;
  readonly end: number;
}

export function getSpan(s: Span): Span { return s; }

export function length(s: Span): number {
  const { start, end } = s;
  return end - start;
}

export function renamed(s: Span): number {
  const { start: by, end: match } = getSpan(s);
  return match - by;
}

export function update(s: Span): number {
  let { end } = s;
  end = end + s.start;
  return end;
}

export function captured(s: Span): number {
  const { end } = s;
  function add(x: number): number { return x + end; }
  return add(s.start);
}

export function loop(s: Span, xs: ReadonlyArray<number>): number {
  const { end } = s;
  let total = 0;
  for (const x of xs) { total = total + x + end; }
  return total;
}

export interface OptionalSpan { readonly end: number | null; }

export function narrowed(s: OptionalSpan): number {
  const { end } = s;
  if (end !== null) { return end; }
  else { return 0; }
}

export interface Box { readonly start: bigint; }

export function sorted(s: Box, xs: ReadonlyArray<bigint>): ReadonlyArray<bigint> {
  const { start: by } = s;
  return xs.toSorted((a, b) => 0);
}
