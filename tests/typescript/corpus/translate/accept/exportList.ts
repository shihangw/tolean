interface Range {
  readonly lo: bigint;
  readonly hi: bigint;
}

function width(r: Range): bigint {
  return r.hi - r.lo;
}

export type Size = bigint;

// An export list adds nothing to the output: the names stay in scope.
export { width, type Range };
