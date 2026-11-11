// expect: 3:16 array destructuring is not supported in a counted 'for'
// A pattern in the first part of a counted loop is not supported.
for (const [a] = [1]; ;) {}
