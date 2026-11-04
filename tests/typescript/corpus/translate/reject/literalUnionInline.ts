// expect: 2:22 a literal union needs a name; declare it as a type, such as type T = 'a' | 'b'
export function f(s: 'a' | 'b'): boolean { return s === 'a'; }
