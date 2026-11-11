// expect: 3:13 a ',' before the ']' of an array pattern
// A hole at the end of an array pattern would print as a trailing ','.
const [a, , ] = [1, 2, 3];
