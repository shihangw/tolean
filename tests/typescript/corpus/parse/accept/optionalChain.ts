// `?.` is one step of a chain. The parser reads the rest of the chain after
// it, as tsc does; the translator refuses that rest.
export const a1 = a?.b;
export const a2 = a?.b?.c;
export const a3 = a?.b.c;
export const a4 = (a?.b).c;
export const a5 = a?.b ?? c;
export const a6 = a?.if;
