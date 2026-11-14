// expect: 2:24 return types of arrow functions are not supported
const add = (x: bigint): void => {
  console.log(x);
};
