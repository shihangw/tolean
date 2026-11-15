// expect: 3:10 date-time forms need an explicit UTC offset
export function f(): number {
  return Date.parse("2000-01-01T12:00:00");
}
