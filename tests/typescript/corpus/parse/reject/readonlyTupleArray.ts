// expect: 2:10 'readonly' is supported only before a tuple type
type T = readonly [bigint, string][];
