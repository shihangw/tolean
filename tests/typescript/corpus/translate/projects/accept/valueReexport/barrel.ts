// The re-export binds no name here, so this file may keep its own private
// function with the same name. A file that imports `double` from this one
// gets the function of origin.ts.
function double(n: bigint): bigint {
  return n;
}

export function same(n: bigint): bigint {
  return double(n);
}

export { double, Color } from "./origin.ts";
