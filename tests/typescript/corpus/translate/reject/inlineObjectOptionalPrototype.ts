// expect: 3:3 an optional field may not be named 'toString'
export type OptionalPrototype = {
  toString?: bigint;
};
