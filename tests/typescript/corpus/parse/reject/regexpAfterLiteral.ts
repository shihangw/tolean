// expect: 2:44 a character-class range is out of order
export const a = /(?:a)/; export const b = /(?:[z-a])/;
