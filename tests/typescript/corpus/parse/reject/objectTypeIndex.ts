// expect: 1:14 mapped types and index signatures are not supported
type Bad = { [key: string]: bigint };
