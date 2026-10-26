// expect: 2:30 tsc may read this 'async(…) :' as an arrow function
export const x = c ? async() : 0
