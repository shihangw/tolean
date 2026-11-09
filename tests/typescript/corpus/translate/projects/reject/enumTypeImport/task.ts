// An import with `type` binds no value, so the members cannot be read.
import type { Status } from "./status.ts";

export function first(): Status {
  return Status.Active;
}
