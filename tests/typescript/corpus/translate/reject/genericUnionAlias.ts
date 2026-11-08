// expect: 2:1 a union of string literals, primitive types or interfaces, or a Record, may not have type parameters
type Color<T> = 'red' | 'green';
