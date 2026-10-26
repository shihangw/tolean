export interface Gauge {
  readonly level: bigint;
  readonly max: bigint;
}

export function raise(g: Gauge, step: bigint): Gauge {
  if (g.level + step > g.max) {
    return { level: g.max, max: g.max };
  }
  return { level: g.level + step, max: g.max };
}
