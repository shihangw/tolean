// expect: 2:32 tsc may read this token after 'satisfies' as a part of the type
export const x = y satisfies T ? 1n : 2n;
