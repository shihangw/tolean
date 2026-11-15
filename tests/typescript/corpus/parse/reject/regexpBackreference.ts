// expect: 2:18 regular expression backreferences are not supported
export const r = /(?:([a])\1)/;
