export type Id = | string
export type Ids = ReadonlyArray<Array<Id>>
export type Grid = (number | null)[][]
export type Flag = 'on' | 'off' | true | 1 | 2n | null | undefined | void
export interface Box {
  readonly items: Ids,
  readonly?: boolean
  label?: string;
  readonly default: unknown
}
export function first(grid: Grid): Map<string, Array<Array<bigint>>> {
  let empty: Array<number>= []
  return grid[0]
}
