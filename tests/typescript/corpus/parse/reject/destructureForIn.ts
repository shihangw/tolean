// expect: 3:16 'for … in' loops are not supported
// A pattern before 'in' starts a 'for … in' loop.
for (const [a] in { b: 1 }) {}
