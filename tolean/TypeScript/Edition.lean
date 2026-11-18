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

An optional nullable annotation is erased before runtime. Its three values
use Undefined and Null (ES2015 and ES2024 §6.1.2 and §6.1.3).
Reading an absent field uses OrdinaryGet (ES2024 §10.1.8.1), and omitted
arguments use FunctionDeclarationInstantiation (§10.2.11). These operations
are available in every supported target. Coalescing and optional chaining
retain their existing ES2020 gates (§13.13.1 and §13.3.9 in ES2024).

A counted `for` loop uses `ForStatement` and `ForBodyEvaluation`
(ES2024 §14.7.4.2). ES2015, the oldest supported target, specifies these
operations.

A feature whose meaning changes in a later edition gets a new feature for the
new meaning, never a second meaning for the same one. An edition joins `all`
only after a review of what it changed.

TypeScript's `parameter is Type` return annotation is erased before runtime.
It adds no ECMAScript feature or edition gate. Its function declaration uses
`FunctionDeclaration` (ES2015 §14.1, ES2024 §15.2), and a strict tag test uses
`Strict Equality Comparison` (ES2015 §7.2.13, `IsStrictlyEqual` in ES2024
§7.2.15). Both are available in every target that this module lists.
Generic function type parameters and interface declarations are erased before
runtime too. The remaining function declaration uses `FunctionDeclaration`
(ES2015 §14.1, ES2024 §15.2), and a call uses `EvaluateCall` (ES2024
§13.3.6.2). These operations exist in every supported target, so generic
certificates add no edition gate.

Try statements with a catch binding use TryStatement and CatchClause
(ES2015 §13.15; ES2024 §14.15). Every supported target includes them.
The initial subset requires a catch binding and does not include `finally`
or the optional catch binding introduced in ES2019.

Structural recursion adds no runtime operation. Its calls use `EvaluateCall`
(ES2015 §12.3.4, ES2024 §13.3.6.2), and recursive interfaces erase with the
other TypeScript type declarations. Every supported edition specifies the
runtime operation.

Flat object binding patterns use BindingInitialization and
KeyedBindingInitialization (ES2015 §13.3.3.5 and §13.3.3.7; ES2024 §14.3.3.3
and §14.3.3.4). They evaluate the source once and read the named properties
in source order. Every supported edition has these operations. Defaults,
nested patterns and destructured parameters remain refused. Object rest is
a separate ES2018 operation and remains refused too.

Guard calls use `EvaluateCall` (ES2024 §13.3.6.2), and their branches use
`IfStatement` (§14.6). A primitive guard uses `typeof` (§13.5.3). These
operations also exist in ES2015, the oldest target.

The annotation `T | undefined` erases at runtime. Its optional value uses the Undefined
type (ES2015, §6.1.1; unchanged in ES2024), and a strict test of it uses
IsStrictlyEqual (ES2024 §7.2.15). These operations need no edition gate because
every supported edition specifies them.

A type-only re-export erases before execution. Its module dependency follows
the ExportDeclaration grammar (ES2015 §15.2.3; ES2024 §16.2.3). It introduces
no local binding and preserves the type's identity in the defining module.

Optional element access follows OptionalExpression and ChainEvaluation
(ES2020 §12.3.9; ES2024 §13.3.9). An absent receiver skips the index and
gives undefined. A present array uses the existing array-index operation.

Expression narrowing follows the strict equality test and the selected
branch of LogicalANDExpression, LogicalORExpression and ConditionalExpression
(ES2024 §13.13 and §13.14). Logical NOT (§13.5.7) reverses the test. ES2015
already specifies these operations, so all supported targets allow them.

Ordinary readonly classes use ClassDefinitionEvaluation (ES2024 §15.7.14),
ClassFieldDefinitionEvaluation (§15.7.13), InitializeInstanceElements
(§7.3.33), and EvaluateNew (§13.3.5.1). Public field declarations require
ES2022. The accepted slice has no observable prototype lookup: elaboration
replaces construction and statically resolved methods before evaluation.

Indexed access annotations erase before execution. TypeScript 2.1 introduced
them; the TypeScript Handbook describes them under Indexed Access Types.
Resolving a literal string key adds no runtime operation or edition gate.
Reading the corresponding field uses OrdinaryGet (ES2024 §10.1.8.1), which
also exists in ES2015. A comparison of its value uses IsStrictlyEqual
(ES2024 §7.2.15; Strict Equality Comparison in ES2015 §7.2.13).

An error constructor may assign a separately declared readonly field from
its same-name parameter after `super(message)`. The annotation erases before
execution. The assignment uses `PutValue` (ES2015 §6.2.3.2, ES2024 §6.2.5.6),
and the derived constructor uses `SuperCall` (ES2015 §12.3.5, ES2024 §13.3.7).
These operations exist in every supported edition. Native field declarations
use `InitializeInstanceElements` (ES2022 §7.3.33) after `super` returns.
The accepted constructor cannot observe the intermediate undefined values,
so its final fields agree with the existing parameter-property model.
Both field forms refuse `__proto__`: downlevel assignment invokes the
inherited setter rather than defining an own field. Plain parameters with
that name remain legal because they do not assign a field.
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
  | readonlyClasses
  /-- The counted `for` loop: `ForStatement` and `ForBodyEvaluation`
  (§14.7.4.2 in ES2024). -/
  | countedFor
  /-- A local call returns a value and writes captured bindings:
  [[Call]] (§10.2.1), SetMutableBinding (§9.1.1.1.5), and ReturnStatement
  (§14.10), with section numbers from ES2024. ES2015 is the oldest target. -/
  | localReturnState
  /-- Calls between local declarations: FunctionDeclarationInstantiation
  (§10.2.11) and [[Call]] (§10.2.1), with ES2024 section numbers. -/
  | localSiblingCalls
  /-- Flagless RegExp patterns and `test`: Pattern Semantics, RepeatMatcher
  and RegExpBuiltinExec (ES2024 §22.2.2, §22.2.2.3.1 and §22.2.7.2).
  The translator accepts flagless literals and their `test` method from ES2015. -/
  | regexp
  /-- String.prototype.replace and RegExp.prototype[@@replace],
  with a literal replacement without GetSubstitution tokens
  (ES2024 §22.1.3.19, §22.2.6.11 and §22.1.3.19.1). -/
  | regexpReplace
  /-- A call changes an exclusively owned Map argument: `EvaluateCall`,
  `OrdinaryCallBindThis`, `FunctionDeclarationInstantiation`,
  `Map.prototype.set`, `Map.prototype.delete` and `ReturnStatement`.
  Copying the final map back
  models the shared object without exposing an alias. Maps date to ES2015. -/
  | mapBorrow
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
  | .readonlyClasses => .es2022
  | .countedFor => .es2015
  | .regexp => .es2015
  | .regexpReplace => .es2015
  | .stringNumberArguments => .es2015
  | .dateParseFormat => .es2016
  | .localReturnState | .localSiblingCalls => .es2015
  | .mapBorrow => .es2015
  | .exponent | .arrayIncludes | .trimWhiteSpace => .es2016
  | .stringPad => .es2017
  | .objectSpread => .es2018
  | .trimStartEnd | .stableSort => .es2019
  | .bigint | .bigintDivision | .bigintBitwise | .nullishCoalescing | .optionalChaining => .es2020
  | .logicalAssignment | .numericSeparators => .es2021
  | .arrayAt | .stringAt => .es2022
  | .arrayFindLast | .arrayToSorted => .es2023

def Feature.describe : Feature → String
  | .readonlyClasses => "ordinary readonly classes"
  | .countedFor => "a counted 'for' loop"
  | .localReturnState => "a local function that returns a value and changes captured variables"
  | .localSiblingCalls => "calls between local functions"
  | .regexp => "regular expressions without flags"
  | .regexpReplace => "regular expression replacement without substitutions"
  | .mapBorrow => "a call that changes an exclusively owned Map argument"
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

-- Inline object-type annotations erase before runtime, so they add no edition
-- gate. Their values use Object Initializer (ES2015 §12.2.6, ES2024 §13.2.5)
-- and Property Accessors (ES2015 §12.3.2, ES2024 §13.3.2). An omitted optional
-- field uses OrdinaryGet (ES2024 §10.1.8.1). A named union of anonymous shapes
-- uses the existing strict tag tests and SwitchStatement (ES2024 §14.12).
-- Every supported target has these operations.
