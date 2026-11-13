// expect: 3:1 an error class may not be named error, the constructor of Thrown for new Error(message)
// Thrown.error holds the JSError of throw new Error(m), so a class cannot take the name.
export class error extends Error {}
export function f(n: bigint): bigint { return n; }
