// The output names JSString.lt, though this file names no string type and
// has no string literal, so it imports the string model.
import type { Entry } from './entry.ts';

export function sorted(e: Entry): boolean {
  return e.key < e.other;
}
