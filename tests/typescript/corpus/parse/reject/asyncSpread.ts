// expect: 3:23 tsc may read this 'async(…)' with a spread as an arrow function's parameters
// JavaScript reads a call with a spread argument; tsc reads the start of an async arrow function.
export const x = async(...[1]);
