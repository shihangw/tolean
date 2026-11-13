// expect: 4:79 the message of an error class may not call a function; it is an expression over the parameters of the constructor
// Thrown comes before the functions of the file, so a message cannot call one.
export function tag(n: bigint): string { return "t"; }
export class WithCall extends Error { constructor(readonly n: bigint) { super(tag(n) + "!"); } }
export function f(n: bigint): bigint { return n; }
