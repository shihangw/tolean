// expect: a call with number-sort preconditions in unsupported tagged narrowing scope
interface Present { readonly kind: "present"; readonly values: ReadonlyArray<number>; }
interface Absent { readonly kind: "absent"; }
type Input = Present | Absent;
function sorted(xs: ReadonlyArray<number>): number[] {
  return xs.toSorted((a, b) => a - b);
}
export function narrowed(input: Input): ReadonlyArray<number> {
  if (input.kind === "present") {
    return sorted(input.values);
  }
  return [];
}
