// An error class may be exported by an export list, as a function may. No
// file can import one yet, so the list changes nothing for it.
class NotFound extends Error {}
export { NotFound };
export function f(x: bigint): bigint {
  if (x < 0n) throw new NotFound("neg");
  return x;
}
