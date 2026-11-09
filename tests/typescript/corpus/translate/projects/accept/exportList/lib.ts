interface Range {
  readonly lo: bigint;
  readonly hi: bigint;
}

function clamp(x: bigint, r: Range): bigint {
  if (x < r.lo) {
    return r.lo;
  }
  if (x > r.hi) {
    return r.hi;
  }
  return x;
}

function helper(x: bigint): bigint {
  return x + 1n;
}

export function next(x: bigint, r: Range): bigint {
  return clamp(helper(x), r);
}

// An export list exports the declarations before it, as `export` before each
// would.
export { clamp, type Range };
