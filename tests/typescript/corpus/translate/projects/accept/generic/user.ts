// Importing from a generic file makes this file generic too.
import { one, twice } from "./num.ts";

export function two(): bigint {
  return one() + one();
}

export function four(x: number): number {
  return twice(twice(x));
}
