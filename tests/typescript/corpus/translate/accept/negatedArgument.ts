// A negation passed to a call needs parentheses in Lean: `fn0 !(false) none`
// would read as `fn0 !((false) none)`. Found by the fuzz, seed 965799910.
export function fn0(p0: boolean, p1: number | null): bigint {
  return 0n;
}
export function fn1(): bigint {
  const v1 = fn0(!false, null);
  return v1;
}
