// expect: 3:45 the parentheses in a substitution of a template literal do not match
// Node: SyntaxError: Missing } in template expression.
export function text(): string { return `${1) + (2}`; }
