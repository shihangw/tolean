// expect: 3:18 indexed access types are not supported
interface Shape { readonly kind: string; readonly size: number; }
type Both = Shape['kind' | 'size'];
