// expect: 3:3 an optional field may not be named 'valueOf'
interface Item {
  readonly valueOf?: bigint;
}
