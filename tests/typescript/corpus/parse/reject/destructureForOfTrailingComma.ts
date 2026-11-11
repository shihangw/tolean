// expect: 3:16 a ',' before the ']' of an array pattern
// The head of a loop refuses the same patterns as a declaration.
for (const [a, ] of [[1]]) {}
