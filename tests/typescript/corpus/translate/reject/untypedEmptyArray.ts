// expect: 2:57 an empty array needs a declared type
export function f(): ReadonlyArray<bigint> { const xs = []; return xs; }
