export function f(): ReadonlyArray<bigint> { const xs: Array<bigint> = []; const alias = xs; xs.push(1n); return alias; }
