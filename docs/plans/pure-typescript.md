# Plan: translate the pure TypeScript that real modules use

**Status:** in progress · **Date:** 2026-11-03

Pure TypeScript in practice uses much more of the language than the subset
accepts. A function is pure when it does no input or output and depends only
on its arguments. But the subset refused generics, recursion, callbacks,
closures, exceptions, `Map`, `switch` and template literals, and pure code
uses all of them. A survey of one pure module of about 2,000 lines, which
folds a list of events into a state, found the features below in almost
every file. Tolean could translate none of its fourteen files. Only two small
functions went through, after someone rewrote them into the subset. What
Tolean translates now is in the [TypeScript guide](../typescript/README.md).

This plan lists what to add so that such a module translates without a
rewrite. It also states the rules that each addition must keep, and the
behavior that Tolean must still refuse.

## The rules for every addition

Every new construct keeps three rules. A construct that cannot keep them
stays refused, even when the code that uses it is pure.

1. **ECMA-262 specifies the behavior, and it is deterministic.** The spec
   must define the result, and the result must be the same in every edition
   that a target allows. Each construct records the edition that added it and
   the section that defines it, in `tolean/TypeScript/Edition.lean`. The
   section numbers in this plan are those of ES2024. Behavior
   that the spec leaves to the engine, the locale or the time zone stays
   refused.
2. **The translation sees every change to state.** The translation is a
   shallow embedding, so a Lean value cannot change behind a name. A `Map`, a
   `Set`, a `Date` and a class instance are references in JavaScript, so two
   names can point to one object. Each of them gets the ownership rule that
   arrays have now: only the function that created the object may change it,
   and nothing else may hold it while it changes.
3. **The proof of the translator still covers it.** Each construct extends
   the Tolean IR, its evaluator and the interpreter, so `program_sound` holds
   for programs that use it. `tests/typescript/interpreter.test.ts` checks
   the interpreter against Node on random programs that use it. Both
   translators give the same output, byte for byte.

## What to add

The tables group the constructs by the stage that adds them. Each row says
what the Lean output is, and what Tolean refuses so that the translation stays
exact. A construct leaves these tables when Tolean translates it, and the
[TypeScript guide](../typescript/README.md) documents it from then on.

### Types and narrowing

| TypeScript | Lean | Refused |
|---|---|---|
| `T \| undefined` as the type of a local or of a return value, and a test such as `x !== undefined && x > 0n` that narrows an optional value inside an expression | `Option T` | `'x' in obj`, which can tell a missing key from `undefined` |
| A chain after `?.`, such as `a?.b.c`, and `a?.[i]` and `f?.()` | `Option.bind` | `==` against anything except `null` and `undefined` |
| `export { … }` and re-exports | Nothing: the names stay in scope | `export *` |
| `as const` and `satisfies` | Nothing: they only check types | `as T` and the non-null assertion `x!`, because TypeScript does not check them |
| A type guard `x is T` | A `Bool` function | A guard whose body the translator cannot show to be a test of the tag |

### Functions

| TypeScript | Lean | Refused |
|---|---|---|
| An arrow function passed to a function of the program, which reads only `const` values and parameters. The translator accepts arrow functions now only as the callback of an array method. | `fun` | A callback that changes a variable outside itself |
| A local function or arrow function stored in a `const` and called later, which changes `let` variables of the enclosing function | A Lean function that takes those variables and returns their new values. The translator lifts it out and threads the variables through each call. | A local function that escapes: one that is returned, stored in a field or passed on |
| A function-typed field or parameter, such as a comparator in an options object | A field of a function type | A function value that changes state when it is called |
| A destructured parameter, such as `{ a, b }: Options` | A pattern on the structure | Defaults inside the pattern |
| A default parameter value | `Option` with a default at the call | A default that reads another parameter |
| `for (let i = a; i < b; i++)` | A fold whose state records that the loop stopped | A `for` loop of another shape, and labels |
| `while` and `do … while`, with a `@decreases` tag that names a measure | A recursive function with `termination_by`, as for recursion below | A loop without such a measure |
| A rest parameter `...xs: T[]`, and a spread argument `f(...xs)` | A `List T` argument | A spread argument to a function whose parameters are not a rest parameter |
| A class with `readonly` fields and methods that do not change `this` | A structure and one function per method | Methods that change `this`, inheritance other than from `Error`, getters, setters and `static` state |


### Generics

| TypeScript | Lean | Refused |
|---|---|---|
| A type parameter with a constraint, such as `T extends Named` | Nothing in the first version | All constraints, until the open question below is settled |

A generic function's type parameters are implicit arguments of its `def`, as
the number type `N` is. A generic interface's become arguments of its
`structure`. A constraint is harder, because TypeScript checks it by the
shape of a type and Lean has no subtyping by shape.

### Recursion

| TypeScript | Lean | Refused |
|---|---|---|
| A function that calls itself on a part of its argument, such as the rest of a list or a child of a tree node | A `def` with structural recursion. Lean checks that it ends without help. | |
| Other recursion, with a `@decreases` JSDoc tag that names a measure | A `def` with `termination_by` that measure. Lean must prove that each call makes the measure smaller, and the translator refuses the file when Lean cannot. | Recursion without such a proof |
| Functions in one file that call each other | A `mutual` block | Recursion across files |
| An interface that refers to itself, such as a tree node with `children: ReadonlyArray<Node>` | A nested `inductive` | |

Lean also accepts `partial def` without a proof that the function ends. But
Lean cannot prove anything about a partial function, so Tolean never writes
one. A JavaScript call can also fail where the Lean function does not: deep
recursion makes Node throw a `RangeError` when the stack runs out. So a claim
about a recursive function holds when the JavaScript call returns, as every
value claim already does.

### Arrays

| TypeScript | Lean | Refused |
|---|---|---|
| `reduce`, `findIndex`, `findLast`, `slice`, `entries` | The `List` functions with the same meaning | The `index` and `array` arguments of a callback, until a later step adds them |
| `includes` | `List.contains` with SameValueZero, which treats `NaN` as equal to itself | |
| `[...xs]`, `[...xs, x]`, and array destructuring | `List.append` and patterns | Spread of anything that is not an array |
| `xs.length`, `xs[i]` and `xs.at(i)` (§23.1.3.1) | `List.length`, and `xs[i]?` of type `Option T`. An index outside the array gives `undefined`. | `xs[i]` in a project without `noUncheckedIndexedAccess`, because there TypeScript types the result as `T` although it can be `undefined` |
| `{ ...a, f: e }`, where `a` has the declared interface of the result | `{ a with f := e }`. The spread keeps the keys of `a` in their order, so the result keeps the declared order. | Spread of an object of another type, which can change the order of the keys |
| `[...xs].sort(cmp)` and `xs.toSorted(cmp)` | A stable merge sort. ECMA-262 has required a stable sort since ES2019 (§23.1.3.30). | `sort` on an array that the function does not own, and a comparator that is not consistent |

A comparator is consistent when it orders values as a total preorder. The
spec leaves the result undefined for any other comparator, so the translator
must refuse it or prove it consistent. The first version accepts two shapes
whose consistency Tolean proves once: a comparison of integer keys, and a
chain of such comparisons. A comparator such as `(a, b) => a.t - b.t` on
`number` keys is consistent only when no key is `NaN`, so it becomes a
precondition of each claim.

### Errors

| TypeScript | Lean | Refused |
|---|---|---|
| `throw new Error(message)` and `throw` of a declared error class | `Except E`. A function that can throw returns `Except`, and its callers pass the error on. | `try` and `catch` in the first version |
| A class that extends `Error` and only sets `readonly` fields in its constructor | A structure | Methods, `static` members, and reads of `stack` |

ECMA-262 does not define `Error.prototype.stack`, so a read of `stack` stays
refused. A claim about a function that can throw says what holds when the
function returns normally. A separate claim can show that it does not throw
when its inputs meet a precondition. The plan for [shared monad
pieces](shared-core.md) adds exceptions to the IR, and this stage uses them.

### Strings

Tolean translates `string` to `JSString`, the list of a string's UTF-16 code
units, and `===` compares the lists. [A decision
record](../decisions/2026-11-06-jsstring.md) explains why. Each operation
below becomes a function on that list, written from its algorithm in the
spec.

One part of the model is left. The lexer refuses a literal that holds a lone
surrogate, such as `"\uD800"`, because the syntax tree keeps the text of a
literal as a Lean `String`. Such a literal should print its code units.

| TypeScript | Lean | Refused |
|---|---|---|
| `<`, `<=`, `>` and `>=` on strings | Lexicographic order on code units, as IsLessThan defines it (§7.2.13) | `localeCompare`, which depends on the locale |
| `+` on strings, and template literals whose parts are `string`, `boolean`, `bigint` or a safe integer `number` | `List.append`. Numbers and `bigint` values convert to ASCII digits (§6.1.6.1.20 and §6.1.6.2.21). | A part that is a non-integer `number` or an object |
| `length`, `at` (§22.1.3.1), `slice` (§22.1.3.22), `startsWith`, `endsWith`, `includes`, `indexOf`, `split` with a string separator (§22.1.3.23), `padStart`, `padEnd` and `trim` | Functions on the list of code units. `slice` and `at` follow the spec for negative and out-of-range indexes. | `split` with a regular expression, and every regular expression in the first version |
| `for (const c of s)` and `[...s]` | Iteration by code point, which joins each surrogate pair (§22.1.3.36 and §22.1.5) | |
| `toUpperCase` and `toLowerCase` (§22.1.3.30 and §22.1.3.28) | Only for strings that the translator can show are ASCII | `normalize` (§22.1.3.15), and case changes of other strings, because their results follow the Unicode version of the engine, and that version changes between Node releases |
| `JSON.stringify(x)` | An opaque function | |

`JSON.stringify` is deterministic and fully specified (§25.5.2), but a model
of it is large. Code calls it mostly to build error messages. The first
version makes it a function that the generated Lean declares but never
defines. A theorem then cannot depend on the text that it returns, so every
theorem still holds for the real function. A claim about the text needs the
full model, which a later step can add.

### Maps and sets

| TypeScript | Lean | Refused |
|---|---|---|
| `new Map()`, `new Set()`, `get`, `has`, `set`, `add`, `delete`, `size`, and `for … of` over them | A list of entries in insertion order. ECMA-262 fixes that order (§24.1 and §24.2). | Keys that are objects, and `number` keys that can be `NaN` or `-0` |
| A function that changes a map that its caller passes in | A function that returns the new map. The caller takes the result in place of the old map. | A call where the caller keeps another name for the same map |

The second row is the borrow that Aeneas uses for Rust. It is sound here only
because the translator checks that the caller owns the map and holds no other
name for it during the call. Key equality is SameValueZero. For `string` and
`bigint` keys that is Lean's equality. For `number` keys it is Lean's
equality only when no key is `NaN` or `-0`.

### Numbers and dates

| TypeScript | Lean | Refused |
|---|---|---|
| `Math.min`, `Math.max`, `Math.floor`, `Math.ceil`, `Math.trunc` (§21.3.2.35), `Math.round` (§21.3.2.28), `Math.abs`, `Number.isInteger`, and `/` on `number` | New `JSNumber` operations, with laws for safe integers and for `NaN` and the infinities | `Math` functions whose results the spec allows to differ between engines, such as `Math.sin` (§21.3.2) |
| `**` on `bigint` (§6.1.6.2.3), and the bitwise operators on `bigint` | The same operations on `Int` | `**` with a negative exponent, and `>>>`, because both throw on a `bigint` |
| `BigInt(n)` (§21.2.1.1) and `Number(b)` (§21.1.1.1) | Conversions. `BigInt(n)` throws a `RangeError` when `n` is not an integer, so it uses the `Except` from the errors stage. | `Number(b)` on a `bigint` that is not a safe integer, until the model rounds to the nearest double |
| The bitwise operators on `number` | `ToInt32` (§7.1.6) and the operation on 32-bit integers | |
| `Object.is` (§20.1.2.15) | SameValue (§7.2.10), which tells `NaN` and `-0` apart | |
| `new Date(t).toISOString()`, `Date.UTC`, `getTime`, and the UTC getters | A model of the time value (§21.4.1) | Local-time getters, setters, and `Date.now()` |
| `Date.parse(s)` | Only when the translator can show that `s` is in the Date Time String Format (§21.4.1.32) | Any other string, because the spec leaves its result to the engine |

`toISOString` throws a `RangeError` for an invalid date, so it uses the
`Except` from the errors stage. The new number laws are hypotheses, as the
current ones are. `jsNumberLaws.test.ts` checks each of them on every
maintained Node release line.

## What stays refused

These stay refused after the plan is done, because no translation of them can
be exact:

- `localeCompare`, `Intl`, and every local-time `Date` method, because their
  results depend on the host.
- `Date.now()`, `Math.random()` and `crypto`, because they are not
  deterministic. The [effects plan](effects.md) makes them inputs.
- `Error.prototype.stack`, and every other property that ECMA-262 does not
  define.
- `toLocaleString` and the other `toLocale…` methods, and `Number.prototype.toFixed`
  and its relatives until the model of `Number::toString` covers fractions.
- `structuredClone`, `setTimeout` and the other functions that the host
  provides, because ECMA-262 does not define them.
- `Symbol`, `Proxy`, `Reflect`, `eval`, `with`, `arguments`, and getters on
  object literals.
- Assignment to an array's `length`, `delete` on objects, and `Object.assign`
  onto an object that the function does not own.
- `Object.keys`, `Object.entries` and `for … in` on objects with keys that look
  like integers. ECMA-262 lists those keys first, in numeric order
  (§10.1.11.1), so the order differs from the order of the literal. These
  are accepted on objects whose keys the type fixes and none of which looks
  like an integer.

## Steps

Each step ends with all checks green, with both translators in agreement, and
with no change to the output of code that is already in the subset. A fix
for output that Lean does not accept may change it too: the binders of
a loop now carry their types ([#59](https://github.com/shihangw/tolean/pull/59)),
and a `let` of a `T | null` local writes its type where Lean would infer
another ([#63](https://github.com/shihangw/tolean/pull/63)).

Each step has a priority. The P0 steps come first, then the P1 steps, then
the P2 steps. Steps with the same priority keep the order of their numbers.

2. **P0.** Types and narrowing: optional parameters and `undefined` as a
   value, the rest of a chain after `?.`, a `default` that assigns to `never`,
   `export { … }` and re-exports, `as const` and `satisfies`, and `Record`
   over a union of string literals.
3. **P1.** Type guards.
4. **P0.** The other array methods without `sort`, such as `reduce` and
   `slice`, indexing, and object spread.
5. **P0.** Control flow: the counted `for` loop.
6. **P0.** Errors, after step 3 of the [shared core plan](shared-core.md) adds
   exceptions to the IR.
7. **P0.** Local functions that change variables of the enclosing function, by
   lifting them out and threading the variables through each call.
8. **P0.** `Map` and `Set`, with owned values and the borrow for a map that a
   caller passes in.
9. **P1.** Strings: template literals, string order, the string methods,
   iteration by code point, and the opaque `JSON.stringify`.
10. **P1.** Sorting with consistent comparators.
11. **P2.** Recursion: structural recursion and types that refer to themselves
    first, then `@decreases`, mutual recursion, and `while` loops.
12. **P1.** The new number and `bigint` operations, and the `Date` methods.
13. **P2.** Classes with `readonly` fields and methods that do not change
    `this`.

Steps 2 and 4 cover most of the code in the survey. Steps 7 and 8 matter
most for proofs, because a fold over events keeps its state in local
variables and in maps.

## Open questions

- How should a certificate cover a generic function or interface? The
  certifier has no encoder for a type parameter, so a file with either gets no
  certificate. The claim could take an encoder for each type parameter as an
  argument, since the code never looks inside such a value.
- How should a type parameter with a constraint translate? One option is a
  type class that the translator writes for each constraint, with one
  method per field that the constraint names. Another is to pass the
  fields that the function reads as explicit arguments.
- Should `try` and `catch` come in a later step? The survey had none, but much
  other pure code catches its own errors.
- Should a map that a caller passes in become a borrow, as above, or should the
  callee run in a state monad? A borrow keeps the output plain, but it only
  covers a call that changes one map.
- Should `tolean.json` accept imports without the `.ts` extension, for
  projects that use bundler resolution? Tolean refuses them now because Node
  reads an import as a URL.
- Should a comparator that is not one of the two shapes be accepted when the
  project supplies a proof that it is consistent?
- How should the spec model `const` in full? Its environment holds values
  only. Since [#63](https://github.com/shihangw/tolean/pull/63), the spec gives
  no value for a block where a statement after a `const` declaration assigns
  it, which covers `=`, `+=`, `??=` and `++`. A `for (const x of xs)` loop is
  left: an assignment to `x` in the body writes the new value, where Node
  throws a `TypeError`. The translator refuses it, so no certified program
  meets the gap, but `interpreter.test.ts` asks the interpreter to agree with
  Node on every program that it parses. The same check on the loop's body
  would close it. A binding kind in `Eval.Env` would cover every case, but
  then `Agree` and every statement proof would compare kinds too.
