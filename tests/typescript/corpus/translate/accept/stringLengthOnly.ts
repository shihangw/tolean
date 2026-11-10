/**
 * `length` and `indexOf` give numbers, though this file writes no number
 * type, number literal or numeric global. The output still needs the number
 * model and its type parameter.
 */
export function sameLength(a: string, b: string): boolean {
  return a.length === b.length;
}

export function sameIndex(a: string, b: string, p: string): boolean {
  return a.indexOf(p) === b.indexOf(p);
}
