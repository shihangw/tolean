// expect: 2:18 lookaround and named regular expression groups are not supported
export const r = /(?:(?<name>a))/;
