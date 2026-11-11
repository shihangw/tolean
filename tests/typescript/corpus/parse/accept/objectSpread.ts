// Spread properties copy the properties of a value.
interface P { readonly x: bigint; }
const a = { x: 1n, y: 2n };
const b = { ...a };
const c = { ...a, y: 3n };
const d = { z: 0n, ...a, ...b };
const e = { ...f(a), w: a.x };
const g = { ...(c), };
function f(o: P): P { return { ...o }; }
