// `../`, the `.js` extension and no extension all name a `.ts` file.
import { raise } from "../gauge.js";
import type { Gauge } from "./util";

export function raiseTwice(g: Gauge, step: bigint): Gauge {
  return raise(raise(g, step), step);
}
