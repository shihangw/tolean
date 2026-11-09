// A type import of the enum: the file only names its type.
import type { Status } from "./status.ts";

export function same(a: Status, b: Status): boolean {
  return a === b;
}
