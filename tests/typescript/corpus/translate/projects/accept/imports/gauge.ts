// A function and an interface from another file.
import { clamp, type Gauge } from "./lib/util.ts";

export function raise(g: Gauge, step: bigint): Gauge {
  return { level: clamp(g.level + step, 0n, g.max), max: g.max };
}

// A parameter named like a namespace does not capture the imported type.
export function bump(lib: bigint, g: Gauge): Gauge {
  return raise(g, lib);
}
