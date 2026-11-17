// expect: 3:16 'missing' is not a field of Shape
interface Shape { readonly kind: string; }
type Missing = Shape['missing'];
