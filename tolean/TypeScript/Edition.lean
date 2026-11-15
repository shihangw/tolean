/-!
Editions of ECMA-262, the JavaScript standard, and the JS features that Tolean
relies on.

A translation is for one target edition. The parser and the translator refuse a
feature that the target does not have, because Tolean translates the source as
it runs: type stripping leaves the syntax as it is, so the engine must support
it, and the meaning that a translation assumes must be the one the target
specifies.

Each feature names the first edition that specifies it as Tolean reads it, and
the ECMA-262 production or operation that does. Section numbers move between
editions; these names do not.

A feature whose meaning changes in a later edition gets a new feature for the
new meaning, never a second meaning for the same one. An edition joins `all`
only after a review of what it changed.

TypeScript's `parameter is Type` return annotation is erased before runtime.
It adds no ECMAScript feature or edition gate. Its function declaration uses
`FunctionDeclaration` (ES2015 §14.1, ES2024 §15.2), and a strict tag test uses
`Strict Equality Comparison` (ES2015 §7.2.13, `IsStrictlyEqual` in ES2024
§7.2.15). Both are available in every target that this module lists.
Guard calls use `EvaluateCall` (ES2024 §13.3.6.2), and their branches use
`IfStatement` (§14.6). A primitive guard uses `typeof` (§13.5.3). These
operations also exist in ES2015, the oldest target.
-/
namespace tolean.TypeScript

inductive Edition where
  | es2015 | es2016 | es2017 | es2018 | es2019 | es2020 | es2021 | es2022 | es2023 | es2024
  | es2025
deriving BEq, DecidableEq, ReflBEq, LawfulBEq, Repr, Inhabited

def Edition.year : Edition → Nat
  | .es2015 => 2015 | .es2016 => 2016 | .es2017 => 2017 | .es2018 => 2018
  | .es2019 => 2019 | .es2020 => 2020 | .es2021 => 2021 | .es2022 => 2022
  | .es2023 => 2023 | .es2024 => 2024 | .es2025 => 2025

def Edition.all : List Edition :=
  [.es2015, .es2016, .es2017, .es2018, .es2019, .es2020, .es2021, .es2022, .es2023, .es2024,
   .es2025]

def Edition.name (e : Edition) : String := s!"ES{e.year}"

/-- `ES2022` or `es2022`. -/
def Edition.parse? (s : String) : Option Edition :=
  Edition.all.find? fun e => e.name.toLower == s.toLower

/-- ES2024, what Node 22 supports: the oldest Node release line still
maintained. -/
def Edition.default : Edition := .es2024

inductive Feature where
  /-- Flagless RegExp patterns and `test`: Pattern Semantics, RepeatMatcher
  and RegExpBuiltinExec (ES2024 §22.2.2, §22.2.2.3.1 and §22.2.7.2).
  The translator accepts flagless literals and their `test` method from ES2015. -/
  | regexp
  /-- `**` and `**=`: `ExponentiationExpression`. -/
  | exponent
  /-- `{ ...e }`: `PropertyDefinition : ... AssignmentExpression`. -/
  | objectSpread
  /-- bigint literals, the `bigint` type, and its `+ - *` and comparisons:
  the `BigInt` type. -/
  | bigint
  /-- bigint `/` truncates toward zero and `%` takes the sign of the dividend:
  `BigInt::divide` and `BigInt::remainder`. -/
  | bigintDivision
  /-- bigint `**`, `&`, `|`, `^`, `<<`, `>>` and `~`: BigInt::exponentiate,
  BigInt::bitwiseAND, BigInt::bitwiseOR, BigInt::bitwiseXOR,
  BigInt::leftShift, BigInt::signedRightShift and BigInt::bitwiseNOT. -/
  | bigintBitwise
  /-- `??`: `CoalesceExpression`. -/
  | nullishCoalescing
  /-- `x?.f`: `OptionalExpression`. -/
  | optionalChaining
  /-- `&&=`, `||=` and `??=`: logical assignment in `AssignmentExpression`. -/
  | logicalAssignment
  /-- `1_000`: `NumericLiteralSeparator`. -/
  | numericSeparators
  /-- `xs.includes(v)`, which compares by SameValueZero:
  `Array.prototype.includes`. -/
  | arrayIncludes
  /-- `xs.at(k)`, which counts a negative `k` from the end:
  `Array.prototype.at`. -/
  | arrayAt
  /-- `xs.findLast(x => p)`, which looks from the end:
  `Array.prototype.findLast`. -/
  | arrayFindLast
  /-- `s.trim()` with the white space of Unicode 8.0 or later, which ES2016
  names. ES2015 names Unicode 5.1, where U+180E is white space too. -/
  | trimWhiteSpace
  /-- `s.trimStart()` and `s.trimEnd()`: `String.prototype.trimStart` and
  `trimEnd`. -/
  | trimStartEnd
  /-- `s.padStart(n)` and `s.padEnd(n)`: `String.prototype.padStart` and
  `padEnd`. -/
  | stringPad
  /-- `s.at(k)`, which counts a negative `k` from the end:
  `String.prototype.at`. -/
  | stringAt
  /-- Number arguments of string methods: `ToIntegerOrInfinity` (§7.1.5
  in ES2024), and `ToUint32` (§7.1.7) for `String.prototype.split`.
  ES2015 calls the first operation `ToInteger`; the behavior is unchanged. -/
  | stringNumberArguments
  /-- `Date.parse` (§21.4.3.2) on the Date Time String Format
  (§21.4.1.32). Date-only forms use UTC from ES2016 onward. -/
  | dateParseFormat
  /-- `xs.sort(cmp)` keeps the order of elements that `cmp` calls equal:
  `SortIndexedProperties`, which is stable since ES2019. -/
  | stableSort
  /-- `xs.toSorted(cmp)`: `Array.prototype.toSorted`. -/
  | arrayToSorted
deriving BEq, Repr, Inhabited

def Feature.since : Feature → Edition
  | .regexp => .es2015
  | .stringNumberArguments => .es2015
  | .dateParseFormat => .es2016
  | .exponent | .arrayIncludes | .trimWhiteSpace => .es2016
  | .stringPad => .es2017
  | .objectSpread => .es2018
  | .trimStartEnd | .stableSort => .es2019
  | .bigint | .bigintDivision | .bigintBitwise | .nullishCoalescing | .optionalChaining => .es2020
  | .logicalAssignment | .numericSeparators => .es2021
  | .arrayAt | .stringAt => .es2022
  | .arrayFindLast | .arrayToSorted => .es2023

def Feature.describe : Feature → String
  | .regexp => "regular expressions without flags"
  | .exponent => "'**'"
  | .objectSpread => "object spread '...'"
  | .bigint => "bigint"
  | .bigintDivision => "bigint '/' and '%'"
  | .bigintBitwise => "bigint '**' and the bitwise operators"
  | .nullishCoalescing => "'??'"
  | .optionalChaining => "'?.'"
  | .logicalAssignment => "'&&=', '||=' and '??='"
  | .numericSeparators => "numeric separators"
  | .arrayIncludes => "Array.prototype.includes"
  | .arrayAt => "Array.prototype.at"
  | .arrayFindLast => "Array.prototype.findLast"
  | .trimWhiteSpace => "the white space of String.prototype.trim without U+180E"
  | .trimStartEnd => "String.prototype.trimStart and trimEnd"
  | .stringPad => "String.prototype.padStart and padEnd"
  | .stringAt => "String.prototype.at"
  | .stringNumberArguments => "number arguments of string methods"
  | .dateParseFormat => "Date.parse on the Date Time String Format"
  | .stableSort => "a stable Array.prototype.sort"
  | .arrayToSorted => "Array.prototype.toSorted"

def Edition.supports (target : Edition) (f : Feature) : Bool := f.since.year ≤ target.year

/-- Why the target refuses `f`. -/
def Feature.refusal (f : Feature) (target : Edition) : String :=
  s!"the target {target.name} does not have {f.describe} (added in {f.since.name})"

end tolean.TypeScript
