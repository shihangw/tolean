// expect: 3:10 'G' is a type; export it with 'type G'
interface G { readonly x: bigint; }
export { G };
