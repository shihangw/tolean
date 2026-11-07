// expect: 2:29 tsc may read this token after 'as const' as a part of the type
export const x = y as const < z;
