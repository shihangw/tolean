import type { Id, MaybeId } from "./ids.ts";

export function next(id: Id): Id {
  return id + 1n;
}

export function isSet(id: MaybeId): boolean {
  return id !== null;
}
