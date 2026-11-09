// expect: 2:14 type parameters with a default are not supported
type Maybe<T = bigint> = T | null;
