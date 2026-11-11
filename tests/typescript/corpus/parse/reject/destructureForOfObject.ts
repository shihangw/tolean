// expect: 3:12 object destructuring is not supported
// Only an array pattern is supported in the head of a loop.
for (const { a } of [{ a: 1 }]) {}
