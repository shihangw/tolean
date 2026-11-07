// expect: 2:1 no parameter's type names the type parameter 'T', so a call could not fix it
function make<T>(n: bigint): bigint {
  return n;
}
