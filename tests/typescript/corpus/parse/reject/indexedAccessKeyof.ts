// expect: 3:21 an indexed access type requires one literal string key
interface Shape { readonly kind: string; readonly size: number; }
type Values = Shape[keyof Shape];
