import { times3 as t3, twice, Hue } from "./relay.ts";
import { double as dbl, Color as Shade } from "./origin.ts";

// The local name `double` is free here, since the import binds `dbl`.
function double(n: bigint): bigint {
  return n + n;
}

export function six(n: bigint): bigint {
  return t3(twice(n));
}

export function eight(n: bigint): bigint {
  return dbl(double(twice(n)));
}

export function isRed(c: Hue): boolean {
  return c === Shade.Red;
}
