// expect: 4:18 indexed access types are not supported
interface Inner { readonly value: bigint; }
interface Outer { readonly inner: Inner; }
type Leaf = Outer['inner']['value'];
