// expect: 3:46 the parentheses in a substitution of a template literal do not match
// A ( that the substitution leaves open would take the made-up ) after it.
export function text(): string { return `${(1}${2)}`; }
