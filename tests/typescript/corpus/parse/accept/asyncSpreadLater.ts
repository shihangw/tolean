// tsc reads a spread after the first argument of async( as a call, as
// JavaScript does, so the parser reads it too.
export const y = async(1, ...[2, 3]);
