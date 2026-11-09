// expect: 2:12 expected a type parameter, found '>'
function f<>(x: bigint): bigint {
  return x;
}
