// expect: 3:33 'c' is not one of the strings of T
type T = 'a' | 'b';
export function f(): T { return 'c'; }
