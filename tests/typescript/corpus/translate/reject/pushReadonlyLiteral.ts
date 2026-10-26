// expect: 2:86 push is allowed only onto an owned array
export function f(): ReadonlyArray<bigint> { const xs: ReadonlyArray<bigint> = [1n]; xs.push(2n); return xs; }
