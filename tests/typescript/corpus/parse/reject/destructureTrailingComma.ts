// expect: 3:11 a ',' before the ']' of an array pattern
// JavaScript allows a ',' after the last name, and the parser refuses it.
const [a, ] = [1, 2];
