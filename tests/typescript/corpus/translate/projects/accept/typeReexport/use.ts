import type { Point, Count } from "./relay.ts";

export function coordinate(p: Point): Count {
  return p.x;
}
