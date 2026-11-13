import tolean.TypeScript.Spec.Number

/-!
The model of a JS `Date` that `tolean` translates to.

A `Date` holds a time value (ECMA-262 §21.4.1.1): the number of milliseconds
since the start of 1970 in UTC, which is an integer within ±8.64 × 10^15, or
`NaN` for an invalid date. TimeClip makes every time value, and it never gives
`-0`, so `Option Int` holds one exactly: `none` is `NaN`. The subset has no
setters, so a `Date` never changes after `new Date(t)` makes it, and a value
can stand for the object.

The calendar functions follow the abstract operations of ECMA-262 §21.4.1:
Day, DayFromYear, YearFromTime, MonthFromTime, DateFromTime, WeekDay and
the time of day, all on integers. `Date.UTC` follows MakeDay, MakeTime and
MakeDate. Where the spec does Number arithmetic, as in `day × msPerDay +
time`, the model uses the operations of `JSNumber`, so a large argument
rounds as it does in JS. `tests/typescript/date.test.ts` checks the getters,
`new Date(t)` and `Date.UTC` against the JS engine on random arguments.

Editions: every edition Tolean supports. Before ES2017, `Date.UTC` with one
argument is up to the engine, so the translator requires two arguments or
more.
-/
namespace tolean.TypeScript

/-- A `Date`: its time value, or `none` when the date is invalid. -/
structure JSDate where
  time : Option Int
deriving DecidableEq, Repr, Inhabited

namespace JSDate

open JSNumber

/-- msPerDay (§21.4.1.2). -/
def msPerDay : Int := 86400000

/-- The largest time value, 8.64 × 10^15 milliseconds, which is 10^8 days. -/
def maxTime : Nat := 8640000000000000

/-- Day(t): the number of the day that holds `t`, counted from the start of
1970. Lean's `/` on `Int` rounds down for a positive divisor, as `floor` does. -/
def day (t : Int) : Int := t / msPerDay

/-- DayFromYear(y): the number of the first day of the year `y`. -/
def dayFromYear (y : Int) : Int :=
  365 * (y - 1970) + (y - 1969) / 4 - (y - 1901) / 100 + (y - 1601) / 400

/-- The year that holds the day `d`: the largest `y` with `dayFromYear y ≤ d`,
which YearFromTime gives. A year has 365.2425 days on average, so the guess is
at most one year off, and the checks correct it. -/
def yearFromDay (d : Int) : Int :=
  let y := 1970 + (d * 400) / 146097
  if dayFromYear (y + 1) ≤ d then y + 1 else if dayFromYear y ≤ d then y else y - 1

/-- YearFromTime(t). -/
def yearFromTime (t : Int) : Int := yearFromDay (day t)

/-- InLeapYear: the year has 366 days (DaysInYear). -/
def isLeap (y : Int) : Bool := y % 4 == 0 && (y % 100 != 0 || y % 400 == 0)

/-- The day within its year of the first day of the month `m`, from 0, in a
leap year or not. -/
def monthStart (leap : Bool) (m : Nat) : Int :=
  let days : List Int := [0, 31, 59, 90, 120, 151, 181, 212, 243, 273, 304, 334]
  days.getD m 0 + (if leap && m ≥ 2 then 1 else 0)

/-- DayWithinYear(t). -/
def dayWithinYear (t : Int) : Int := day t - dayFromYear (yearFromTime t)

/-- MonthFromTime(t): the month, from 0 for January, as the table of the spec
gives it: the last month whose first day is not after the day within the year. -/
def monthFromTime (t : Int) : Int :=
  let leap := isLeap (yearFromTime t)
  let d := dayWithinYear t
  (((List.range 12).filter fun m => monthStart leap m ≤ d).length : Int) - 1

/-- DateFromTime(t): the day of the month, from 1. -/
def dateFromTime (t : Int) : Int :=
  dayWithinYear t - monthStart (isLeap (yearFromTime t)) (monthFromTime t).toNat + 1

/-- WeekDay(t): the day of the week, from 0 for Sunday. The first day of 1970
was a Thursday. -/
def weekDay (t : Int) : Int := (day t + 4) % 7

/-- HourFromTime(t), MinFromTime(t), SecFromTime(t) and msFromTime(t). -/
def hourFromTime (t : Int) : Int := (t / 3600000) % 24
def minFromTime (t : Int) : Int := (t / 60000) % 60
def secFromTime (t : Int) : Int := (t / 1000) % 60
def msFromTime (t : Int) : Int := t % 1000

variable {N : Type} [JSNumber N]

/-- TimeClip(time): `NaN` for a number that is not finite or is more than
8.64 × 10^15 from zero, and the integer part of the number otherwise. Every
double past 2^52 is an integer, so the test of the size on the integer part
is the test on the number. -/
def timeClip (t : N) : Option Int :=
  (toInt t).bind fun i => if i.natAbs ≤ maxTime then some i else none

/-- `new Date(t)` on a number `t` (§21.4.2.1): the date whose time value is
TimeClip of `t`. -/
def ofNumber (t : N) : JSDate := ⟨timeClip t⟩

/-- A time value as a number: `NaN` for an invalid date. A time value is a
safe integer. -/
def number : Option Int → N
  | none => nan
  | some t => ofSafeInt t

/-- `d.getTime()` and `d.valueOf()` (§21.4.4.10, §21.4.4.44). -/
def getTime (d : JSDate) : N := number d.time

/-- A UTC getter, such as `d.getUTCFullYear()`: `NaN` for an invalid date, and
the field `f` of the time value otherwise. -/
def utcField (f : Int → Int) (d : JSDate) : N := number (d.time.map f)

/-- `d.getUTCFullYear()` and the other UTC getters (§21.4.4). -/
def getUTCFullYear (d : JSDate) : N := utcField yearFromTime d
def getUTCMonth (d : JSDate) : N := utcField monthFromTime d
def getUTCDate (d : JSDate) : N := utcField dateFromTime d
def getUTCDay (d : JSDate) : N := utcField weekDay d
def getUTCHours (d : JSDate) : N := utcField hourFromTime d
def getUTCMinutes (d : JSDate) : N := utcField minFromTime d
def getUTCSeconds (d : JSDate) : N := utcField secFromTime d
def getUTCMilliseconds (d : JSDate) : N := utcField msFromTime d

/-- The name of the function of this file that the method `name` of a date
is, of the methods that take no arguments: `getTime` for `getTime` and
`valueOf`, and the UTC getters under their own names. -/
def methodName? (name : String) : Option String :=
  if name == "getTime" || name == "valueOf" then some "getTime"
  else if ["getUTCFullYear", "getUTCMonth", "getUTCDate", "getUTCDay", "getUTCHours",
      "getUTCMinutes", "getUTCSeconds", "getUTCMilliseconds"].contains name then some name
  else none

/-- The method of a date whose name is `name`, of those that take no
arguments. -/
def method? (name : String) : Option (JSDate → N) :=
  if name == "getTime" || name == "valueOf" then some getTime
  else if name == "getUTCFullYear" then some getUTCFullYear
  else if name == "getUTCMonth" then some getUTCMonth
  else if name == "getUTCDate" then some getUTCDate
  else if name == "getUTCDay" then some getUTCDay
  else if name == "getUTCHours" then some getUTCHours
  else if name == "getUTCMinutes" then some getUTCMinutes
  else if name == "getUTCSeconds" then some getUTCSeconds
  else if name == "getUTCMilliseconds" then some getUTCMilliseconds
  else none

/-- 𝔽(! ToIntegerOrInfinity(x)) of a finite number `x`: its integer part, as
a number. -/
def integerPart (x : N) : N := ofInt ((toInt x).getD 0)

/-- MakeTime(hour, min, sec, ms). -/
def makeTime (h m s ms : N) : N :=
  if !(isFinite h && isFinite m && isFinite s && isFinite ms) then nan
  else
    add (add (add (mul (integerPart h) (ofSafeInt 3600000)) (mul (integerPart m) (ofSafeInt 60000)))
      (mul (integerPart s) (ofSafeInt 1000))) (integerPart ms)

/-- MakeDay(year, month, date). The year and the month fix a month, whose
first day must be a finite time value: an integral number that is exactly
`days × msPerDay`. Otherwise the arguments are out of range, and MakeDay is
`NaN`. -/
def makeDay (year month date : N) : N :=
  if !(isFinite year && isFinite month && isFinite date) then nan
  else
    let m := (toInt month).getD 0
    let ym := add (integerPart year) (ofInt (m / 12))
    match toInt ym with
    | none => nan
    | some y =>
      let days := dayFromYear y + monthStart (isLeap y) (m % 12).toNat
      if toInt (ofInt (N := N) (days * msPerDay)) != some (days * msPerDay) then nan
      else sub (add (ofInt days) (integerPart date)) (ofSafeInt 1)

/-- MakeDate(day, time). -/
def makeDate (day time : N) : N :=
  if !(isFinite day && isFinite time) then nan
  else
    let tv := add (mul day (ofSafeInt 86400000)) time
    if isFinite tv then tv else nan

/-- MakeFullYear(year): a year from 0 to 99 is a year of the 1900s. -/
def makeFullYear (year : N) : N :=
  if isNaN year then nan
  else
    match toInt year with
    | some y => if 0 ≤ y && y ≤ 99 then ofSafeInt (1900 + y) else year
    | none => year

/-- `Date.UTC(year, month, date, hours, minutes, seconds, ms)` (§21.4.3.4) on
the numbers given: the time value as a number. A missing month or time is 0,
and a missing date is 1. A missing year is `NaN`, the number of `undefined`. -/
def utc (args : List N) : N :=
  let arg (i : Nat) (default : N) : N := args.getD i default
  let y := arg 0 nan
  let t := makeDate (makeDay (makeFullYear y) (arg 1 (ofSafeInt 0)) (arg 2 (ofSafeInt 1)))
    (makeTime (arg 3 (ofSafeInt 0)) (arg 4 (ofSafeInt 0)) (arg 5 (ofSafeInt 0)) (arg 6 (ofSafeInt 0)))
  number (timeClip t)

end JSDate

end tolean.TypeScript
