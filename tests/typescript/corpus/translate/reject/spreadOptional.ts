// expect: 5:18 'note' is optional or a tag; after a spread only a required field may be set
// JS appends a key that the spread did not copy, and Lean keeps the declared order.
export interface P { readonly x: bigint; readonly note?: string; }
export function f(p: P, s: string): P {
  return { ...p, note: s };
}
