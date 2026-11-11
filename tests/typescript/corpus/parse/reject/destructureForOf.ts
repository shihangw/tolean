// expect: 3:12 array destructuring is supported only in a 'const' or 'let' statement
// A loop over pairs with a pattern is not supported yet.
for (const [k, v] of [[1, 2]]) {}
