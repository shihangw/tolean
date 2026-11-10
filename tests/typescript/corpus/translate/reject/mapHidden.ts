// expect: 2:1 'Map' would hide the global Map
function Map(): bigint {
  return 1n;
}

export function f(): bigint {
  return 0n;
}
