import { restock, type Fruit, type Stock } from "./stock.ts";

// The key type comes from another file, so the output names its
// constructors with that file's namespace.
export function left(s: Stock, f: Fruit): bigint {
  return restock(s)[f];
}
