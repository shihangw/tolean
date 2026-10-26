// expect: 2:105 an owned array may be read only in the return value
export function f(): ReadonlyArray<bigint> { const xs: Array<bigint> = []; xs.push(1n); for (const x of xs) { xs.push(x); } return xs; }
