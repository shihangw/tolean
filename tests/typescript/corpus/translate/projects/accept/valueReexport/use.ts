import { double, isRed, Color } from "./relay.ts";
import { same } from "./barrel.ts";

export function quadruple(n: bigint): bigint {
  return double(double(n));
}

export function redFirst(red: boolean): boolean {
  return isRed(red ? Color.Red : Color.Blue);
}

export function unchanged(n: bigint): bigint {
  return same(n);
}
