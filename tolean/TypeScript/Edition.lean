/-!
Editions of ECMA-262, the JavaScript standard, and the JS features that tolean
relies on.

A translation is for one target edition. The parser and the translator refuse a
feature that the target does not have, because tolean translates the source as
it runs: type stripping leaves the syntax as it is, so the engine must support
it, and the meaning that a translation assumes must be the one the target
specifies.

Each feature names the first edition that specifies it as tolean reads it, and
the ECMA-262 production or operation that does. Section numbers move between
editions; these names do not.

A feature whose meaning changes in a later edition gets a new feature for the
new meaning, never a second meaning for the same one. An edition joins `all`
only after a review of what it changed.
-/
namespace tolean.TypeScript

inductive Edition where
  | es2015 | es2016 | es2017 | es2018 | es2019 | es2020 | es2021 | es2022 | es2023 | es2024
  | es2025
deriving BEq, Repr, Inhabited

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
  /-- `**` and `**=`: `ExponentiationExpression`. -/
  | exponent
  /-- bigint literals, the `bigint` type, and its `+ - *` and comparisons:
  the `BigInt` type. -/
  | bigint
  /-- bigint `/` truncates toward zero and `%` takes the sign of the dividend:
  `BigInt::divide` and `BigInt::remainder`. -/
  | bigintDivision
  /-- `??`: `CoalesceExpression`. -/
  | nullishCoalescing
  /-- `&&=`, `||=` and `??=`: logical assignment in `AssignmentExpression`. -/
  | logicalAssignment
  /-- `1_000`: `NumericLiteralSeparator`. -/
  | numericSeparators
deriving BEq, Repr, Inhabited

def Feature.since : Feature → Edition
  | .exponent => .es2016
  | .bigint | .bigintDivision | .nullishCoalescing => .es2020
  | .logicalAssignment | .numericSeparators => .es2021

def Feature.describe : Feature → String
  | .exponent => "'**'"
  | .bigint => "bigint"
  | .bigintDivision => "bigint '/' and '%'"
  | .nullishCoalescing => "'??'"
  | .logicalAssignment => "'&&=', '||=' and '??='"
  | .numericSeparators => "numeric separators"

def Edition.supports (target : Edition) (f : Feature) : Bool := f.since.year ≤ target.year

/-- Why the target refuses `f`. -/
def Feature.refusal (f : Feature) (target : Edition) : String :=
  s!"the target {target.name} does not have {f.describe} (added in {f.since.name})"

end tolean.TypeScript
