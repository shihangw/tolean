// certify: required
function sorted(xs: ReadonlyArray<number>): number[] {
  return xs.toSorted((a, b) => a - b);
}

export function looseNull(values?: ReadonlyArray<number> | null): number[] {
  if (values == null) { return []; }
  return sorted(values);
}

export function strictNull(values?: ReadonlyArray<number> | null): number[] {
  if (values === null) { return []; }
  if (values === undefined) { return []; }
  return sorted(values);
}

export function strictUndefined(values?: ReadonlyArray<number> | null): number[] {
  if (values === undefined) { return []; }
  if (values === null) { return []; }
  return sorted(values);
}

export function inCallback(values?: ReadonlyArray<number> | null): boolean[] {
  return [0].map(_ => values == null || sorted(values).length > 0);
}

function classify(value?: number | null): number {
  if (value === undefined) { return 0; }
  if (value === null) { return 1; }
  return value;
}

export function classifyMissing(): number {
  return classify();
}

export function classifyNull(): number {
  return classify(null);
}

export function classifyValue(): number {
  return classify(7);
}
