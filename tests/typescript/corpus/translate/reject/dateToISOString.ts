// expect: 2:45 a Date has no method 'toISOString' in the subset
export function f(d: Date): string { return d.toISOString(); }
