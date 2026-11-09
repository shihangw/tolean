// expect: 2:12 'string' cannot name a type parameter
function f<string>(x: bigint): bigint {
  return x;
}
