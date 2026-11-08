import { type Stock } from "./stock.ts";

// The output would name the constructors of Fruit, which this file does not
// import.
export function apples(s: Stock): bigint {
  return s['apple'];
}
