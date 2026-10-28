// A path may climb out of its directory.
import { raise } from "../gauge.ts";
import type { Gauge } from "./util.ts";

export function raiseTwice(g: Gauge, step: bigint): Gauge {
  return raise(raise(g, step), step);
}
