// expect: 3:26 expected ']'
interface Shape { readonly kind: string; readonly size: number; }
type Both = Shape['kind' | 'size'];
