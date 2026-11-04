// expect: 3:1 'Id' is declared twice
interface Id { readonly value: bigint; }
type Id = bigint;
