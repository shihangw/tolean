// expect: 3:41 a parameter of an error class may not be named message, which Error owns
// JS assigns the parameter property after super() returns, so it would replace the message.
class Named extends Error { constructor(readonly message: string, readonly code: bigint) { super("fixed"); } }
export function f(n: bigint): bigint { return n; }
