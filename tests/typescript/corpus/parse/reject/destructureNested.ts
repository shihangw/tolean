// expect: 3:8 nested destructuring is not supported
// A place of an array pattern is a name, not another pattern.
const [[a]] = [[1]];
