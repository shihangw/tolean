// expect: 3:6 an 'in' in the declaration of a 'for' needs parentheses
// ECMA-262 allows this `in`, but tsc reads `for … in` and refuses the rest.
for (let b = ['k' in o]; ; ) {}
