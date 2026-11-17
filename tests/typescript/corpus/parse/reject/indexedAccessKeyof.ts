// expect: 3:20 indexed access types are not supported
interface Shape { readonly kind: string; readonly size: number; }
type Values = Shape[keyof Shape];
