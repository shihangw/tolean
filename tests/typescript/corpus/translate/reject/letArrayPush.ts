// expect: 2:46 an array that the function pushes to must be
export function f(): ReadonlyArray<bigint> { let xs: Array<bigint> = []; xs.push(1n); return xs; }
