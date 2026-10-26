// expect: 2:42 the elements of an array must have one type
export function f(): bigint { const xs = [1n, true]; return 0n; }
