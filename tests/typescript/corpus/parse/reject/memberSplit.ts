// expect: 5:1 unfinished member access
// tsc reads the name after the line break, with a word after it, as a member
// access that lacks its name. JavaScript reads `a.default instanceof b`.
export const x = a.
default instanceof b;
