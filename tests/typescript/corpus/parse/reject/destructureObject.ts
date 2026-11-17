// expect: 3:7 object destructuring is not supported; bind the source once, then declare each field separately
// The diagnostic gives a rewrite that does not repeat the source evaluation.
const { a } = { a: 1 };
