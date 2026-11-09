// expect: 3:1 a union of string literals, primitive types or interfaces, or a Record, may not have type parameters
type Key = 'a' | 'b';
type Table<T> = Record<Key, T>;
