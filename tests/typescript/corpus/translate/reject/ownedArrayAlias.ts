// expect: 2:90 an owned array may be read only in the return value
export function f(): ReadonlyArray<bigint> { const xs: Array<bigint> = []; const alias = xs; xs.push(1n); return alias; }
