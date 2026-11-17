// expect: 2:17 an indexed access receiver must resolve to a declared interface or object type
type Field<T> = T['kind'];
