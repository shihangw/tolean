// expect: 3:3 an optional field may not also be nullable
interface Item {
  readonly discount?: bigint | null;
}
