type Pair = [string, bigint];
type Frozen = readonly [bigint, boolean, string];
type Nested = readonly [Pair, ReadonlyArray<readonly [bigint, bigint]>];
type Many = [bigint, bigint][];
export function first(p: readonly [bigint, string]): bigint { return p[0]; }
