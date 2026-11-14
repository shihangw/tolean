# Plan: translate the pure TypeScript that real modules use

**Status:** in progress · **Date:** 2026-11-03

Pure TypeScript in practice uses much more of the language than the subset
accepts. A function is pure when it does no input or output and depends only
on its arguments. A survey of one pure module of about 2,000 lines, which
folds a list of events into a state, found generics, recursion, callbacks,
closures, exceptions, `Map`, `switch` and template literals in almost every
file. When the survey ran, Tolean could translate none of its fourteen files.
What Tolean translates now is in the [TypeScript
guide](../typescript/README.md).

This plan lists what is left to add so that such a module translates
without a rewrite. It also states the rules that each addition must keep,
and the behavior that Tolean must still refuse.

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
   shallow embedding, so a Lean value cannot change behind a name. A `Date`
   and a class instance are references in JavaScript, so two names can point
   to one object. Each of them gets the ownership rule that arrays, maps and
   sets have now: only the function that created the object may change it,
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
| `a?.[i]` and `f?.()` | `Option.bind` | `==` against anything except `null` and `undefined` |
| A re-export, such as `export { a } from "./x.ts"` | Nothing: the names stay in scope | `export *` |
| A type guard `x is T` | A `Bool` function | A guard whose body the translator cannot show to be a test of the tag |

### Functions

| TypeScript | Lean | Refused |
|---|---|---|
| An arrow function passed to a function of the program, which reads only `const` values and parameters | `fun` | A callback that changes a variable outside itself |
| A local function that returns a value and also changes `let` variables of the enclosing function | A Lean function that returns the value and the new values of those variables, which the call binds again | A `return` before the last statement of such a function |
| A function-typed field or parameter, such as a comparator in an options object | A field of a function type | A function value that changes state when it is called |
| A destructured parameter, such as `{ a, b }: Options` | A pattern on the structure | Defaults inside the pattern |
| A default parameter value | `Option` with a default at the call | A default that reads another parameter |
| `while` and `do … while`, with a `@decreases` tag that names a measure | A recursive function with `termination_by`, as for recursion below | A loop without such a measure |
| A rest parameter `...xs: T[]`, and a spread argument `f(...xs)` | A `List T` argument | A spread argument to a function whose parameters are not a rest parameter |
| A class with `readonly` fields and methods that do not change `this` | A structure and one function per method | Methods that change `this`, inheritance other than from `Error`, getters, setters and `static` state |

### Generics

| TypeScript | Lean | Refused |
|---|---|---|
| A type parameter with a constraint, such as `T extends Named` | Nothing in the first version | All constraints, until the open question below is settled |

A constraint is hard to translate, because TypeScript checks it by the shape
of a type and Lean has no subtyping by shape.

### Recursion

| TypeScript | Lean | Refused |
|---|---|---|
| Recursion where a call does not pass a part of one parameter, with a `@decreases` JSDoc tag that names a measure | A `def` with `termination_by` that measure. Lean must prove that each call makes the measure smaller, and the translator refuses the file when Lean cannot. | Recursion without such a proof |
| Functions in one file that call each other | A `mutual` block | Recursion across files |
| A tagged union whose members refer to the union, such as `interface Add { readonly kind: 'add'; readonly left: Expr }` with `type Expr = Num \| Add` | A `mutual` block of the structures and the inductive type, which Lean accepts | |

Lean also accepts `partial def` without a proof that the function ends. But
Lean cannot prove anything about a partial function, so Tolean never writes
one. A JavaScript call can also fail where the Lean function does not: deep
recursion makes Node throw a `RangeError` when the stack runs out. So a claim
about a recursive function holds when the JavaScript call returns, as every
value claim already does.

### Arrays

| TypeScript | Lean | Refused |
|---|---|---|
| `entries` | The `List` functions with the same meaning | The `index` argument of a callback other than one of `map`, and the `array` argument of any callback, until a later step adds them |
| `xs.at(i)` and `xs.slice(i, j)` where an argument is not an integer literal (§23.1.3.1, §23.1.3.28) | `ToIntegerOrInfinity` on each argument, then the element or the slice as for literals. It needs `Math.trunc` from the numbers stage. | |
| A certificate for a file that sorts by a `number` key | As for `bigint` and `string` keys, with the precondition that no key is `NaN`, and for a difference that every key is finite. A difference also needs new laws: `<` is a strict total order on numbers that are not `NaN`, and the sign of `a - b` is the order of `a` and `b`. `jsNumberLaws.test.ts` would check them. | |

The certifier writes no precondition today, so such a file gets no
certificate.

### Strings

Each operation below becomes a function on `JSString`, the list of UTF-16
code units that Tolean translates a `string` to, written from its algorithm
in the spec. [A decision record](../decisions/2026-11-06-jsstring.md)
explains the model.

A literal that holds a lone surrogate, such as `"\uD800"`, should print its
code units. The lexer refuses it now, because the syntax tree keeps the text
of a literal as a Lean `String`.

| TypeScript | Lean | Refused |
|---|---|---|
| A number argument of `at`, `slice`, `padStart`, `padEnd`, `startsWith`, `endsWith`, `includes`, `indexOf` or `split` that is not an integer literal | `ToIntegerOrInfinity` on the argument, then the function on code units that a literal gets now. It needs `Math.trunc` from the numbers stage, as `xs.at(i)` does. | `split` with a regular expression, and every regular expression in the first version |

### Maps and sets

| TypeScript | Lean | Refused |
|---|---|---|
| A function that changes a map that its caller passes in | A function that returns the new map. The caller takes the result in place of the old map. | A call where the caller keeps another name for the same map |

This is the borrow that Aeneas uses for Rust. It is sound here only
because the translator checks that the caller owns the map and holds no other
name for it during the call. The spec's call rule now gives no value for a
function that changes a parameter (`Stmt.ownsChanges`), so the borrow must
also give the spec this meaning: the call copies the map in and back out.

One certificate gap is left. The initial value of a `reduce` can read a map
or a set that `new Map(items)` or `new Set(items)` makes from a parameter,
such as `xs.reduce((a, x) => a || x, new Set<bigint>(ys).has(0n))`. The
certifier writes a certificate for it, and Lean refuses that certificate.
The link proof unfolds the constructor only on a list that it can see, so
the set stays `Eval.setOfItems` of an unknown list. A lemma about
`setOfItems` and `mapOfItems` would close the gap. Until then, the certifier
should refuse such an initial value.

### Numbers and dates

| TypeScript | Lean | Refused |
|---|---|---|
| `**` on `bigint` (§6.1.6.2.3) whose exponent is not a literal | `a ^ b.toNat`, after a check that `b` is not negative, which needs the `Except` from the errors stage because JS throws a `RangeError` there | `>>>` on a `bigint`, because it throws |
| `BigInt(n)` (§21.2.1.1) | A conversion that throws a `RangeError` when `n` is not an integer. The message of that error is up to the engine, so it needs the error classes of the errors stage, and a model of an error whose message the program cannot read. | |
| `d.toISOString()` | The Date Time String Format of `JSDate`. It throws a `RangeError` for an invalid date, and the message is up to the engine, so it needs the error classes of the errors stage. | Local-time getters, setters, and `Date.now()` |
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
- `normalize`, and `toUpperCase` and `toLowerCase` on a string that the
  translator cannot show is ASCII, because their results follow the Unicode
  version of the engine, and that version changes between Node releases.
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
for output that Lean does not accept may change that output too.

Each step has a priority. The P0 steps come first, then the P1 steps, then
the P2 steps. Steps with the same priority keep the order of their numbers.
The steps keep the numbers that pull requests refer to, so a finished step
leaves a gap.

2. **P0.** Types and narrowing: `T | undefined` as a type, a test of
   `undefined` that narrows inside an expression, `a?.[i]` and `f?.()`, and
   re-exports.
3. **P1.** Type guards.
4. **P0.** The rest of the arrays without `sort`: `entries`, and `at` and
   `slice` with arguments that are not integer literals.
8. **P0.** The borrow for a map that a caller passes in.
10. **P1.** Sorting: certificates for a sort by a `number` key.
11. **P2.** Recursion: tagged unions that refer to themselves first, then
    `@decreases`, mutual recursion, and `while` loops.
12. **P1.** The new number and `bigint` operations, the `Date` methods, and
    the number arguments of string methods that are not integer literals.
13. **P2.** Classes with `readonly` fields and methods that do not change
    `this`.
14. **P1.** Local functions: one that returns a value and changes variables
    of the enclosing function, calls between local functions, and
    certificates for files that have local functions.

Steps 2 and 4 cover most of the code in the survey. Step 8 matters most for
proofs, because a fold over events keeps much of its state in maps.

## Open questions

Each question ends with a recommendation. A recommendation is not a decision:
the step that takes the question up turns it into a decision record, or finds
a reason to choose otherwise.

- How should a certificate cover a generic function or interface? The
  certifier has no encoder for a type parameter, so a file with either gets
  no certificate. The claim could take an encoder for each type parameter as
  an argument, since the code never looks inside such a value.

  Recommendation: take a codec for each type parameter, not only an encoder.
  The loop lemmas decode the environment back into Lean values, so they need
  a decoder and the round trip `dec (some (enc x)) = x`. A test such as
  `x === null` on a `T | null` needs `enc x ≠ Val.null`, and `??` needs
  `enc x ≠ Val.undefined`. Those are the lemmas that the certifier writes for
  every enum and struct today. One structure `Codec N T` bundles them. The
  theorem of a generic function takes `(c : Codec N T)`, the certifier writes
  `codecGauge : Codec N Gauge` for each concrete type from the same pieces,
  and a generic interface gets a codec constructor such as
  `codecPair (cA : Codec N A) (cB : Codec N B) : Codec N (Pair A B)`. The
  claim holds because the translator refuses every construct that looks
  inside a value of type `T`. If a later construct breaks that, Lean refuses
  the certificate rather than accepting a false one.

- How should a certificate cover an interface that refers to itself, and a
  function that calls itself? The encoder of such an interface would be a
  recursive function, and a certificate runs the interpreter with as much
  fuel as the calls need, which a recursive call does not bound. So a file
  with either gets no certificate yet.

  Recommendation: write the encoder with well-founded recursion, as the
  translated function is written. It recurses through `List.map` over the
  children with `sizeOf` as the measure and the same decreasing tactic. The
  decoder recurses on the `Val`, which is a nested inductive too. The
  round-trip proof is the new work, and the certifier should get it from one
  lemma about a structure whose list field holds the structure, not from a
  tactic script per file. For a recursive function, quantify the fuel
  existentially for each input:

  ```lean
  theorem f_cert (x : Tree) : ∃ n, ∀ fuel, n ≤ fuel →
      run program "f" [encTree x] fuel = some (encTree (f x))
  ```

  The proof follows the function's own `termination_by`: induction on
  `sizeOf x`, where the step takes the largest of the children's fuels. That
  step needs one lemma the library lacks, that more fuel never changes a
  `some` result of the interpreter or of the IR evaluator. The existential
  form composes: a caller of a recursive function gets a claim of the same
  shape. An explicit bound such as `sizeOf x + depth ≤ fuel` would leak into
  every caller's statement.

- How should a certificate cover a counted `for` loop? The interpreter gives
  no value when the counter would pass `Number.MAX_SAFE_INTEGER`, as it
  would for a bound of `Infinity`, so the claim that it gives a value for
  every input does not hold. The claim could take the hypothesis that the
  interpreter gives a value, or that the bound is at most
  `Number.MAX_SAFE_INTEGER`.

  Recommendation: take a hypothesis on the bound, stated over the parameters.
  The translation of a counted loop is the `for … of` fold over
  `JSNumber.countUp k b`, the IR evaluator gives `countUp? k b` and has no
  value when that is `none`, and `countUp` is `countUp?` with `[]` for
  `none`. So the link theorem fails only where `countUp? k b = none`, and
  each counted loop adds one binder to the function's two theorems:

  ```lean
  theorem sum_cert {N : Type} [JSNumber N] (xs : List Int) (n : N)
      (h0 : (JSNumber.countUp? 0 n).isSome) :
      run program "sum" [encList Val.int xs, Val.num n] = some (Val.int (sum xs n))
  ```

  The bound inside `countUp?` is the loop's bound, printed over the
  parameters as the translation prints it. For `i < xs.length` it is
  `JSNumber.ofSafeInt xs.length`, so the hypothesis says that the list has at
  most `Number.MAX_SAFE_INTEGER` elements. One library lemma,
  `countUp?_eq_of_isSome`, rewrites the evaluator's value into
  `some (.list (List.map Val.num (countUp k b)))`, which is the shape the loop
  lemma already proves, so the loop lemma needs no new code. The certifier
  checks that the bound reads only parameters and refuses the other loops. A
  literal bound such as `i < 10` keeps the hypothesis, because the theorems
  hold for an abstract number model and `countUp?` on a literal reduces only
  under the safe-integer laws. A follow-up can cover a bound that is a
  `const` local by inlining the chain of definitions back to the parameters.
  The other hypothesis, that the interpreter gives a value, would need the
  converse of soundness, that a value of the interpreter implies a value of
  the IR evaluator. That is a second proof of the translator and not worth
  its cost.

- How should a type parameter with a constraint translate? One option is a
  type class that the translator writes for each constraint, with one
  method per field that the constraint names. Another is to pass the
  fields that the function reads as explicit arguments.

  Recommendation: the type class. `T extends Named` becomes `[Named T]`, with
  `class Named (T : Type) where name : T → JSString`, and the translator
  writes `instance : Named Person := ⟨Person.name⟩` wherever it checks the
  constraint at a call. The signature then mirrors the TypeScript one, call
  sites stay as they are, `A & B` becomes two instance arguments, and a
  constraint on a generic interface's parameter works, which explicit fields
  cannot do. Explicit fields are dictionary passing by hand, and they change
  every caller. For a certificate, the codec of `T` gains one law per method:
  the object's field holds the encoding of the method's result. The first
  version accepts constraints that are interfaces or object types with
  readonly fields, and refuses primitive bounds. Every instance gets a name,
  so that instance search never has two candidates.

- Should `try` and `catch` come in a later step? The survey had none, but much
  other pure code catches its own errors.

  Recommendation: yes. Once the IR has `Except`, the interpreter
  change is small. The first version takes `try { … } catch (e) { … }` where
  the catch tests `e` with `instanceof` or ignores it, and refuses `finally`,
  a rethrow of a changed value, and a `throw` of anything but an error. The
  locals that the `try` body assigns become its result tuple, as a loop
  body's do and a local function's do
  ([decision](../decisions/2026-11-12-local-functions.md)), so the
  threading that these use is already in place.

- Should a map that a caller passes in become a borrow, as above, or should the
  callee run in a state monad? A borrow keeps the output plain, but it only
  covers a call that changes one map.

  Recommendation: the borrow, with a tuple when a callee changes several
  maps. A callee that changes two maps returns a pair, and one with a result
  returns a triple, as a loop already returns the tuple of the locals it
  changes, and as Aeneas does for Rust. A state monad would hide which maps a
  function touches and bring `StateT` lemmas into every proof about pure
  code. The [effects plan](effects.md) keeps the monad for state that is
  global. The parameter's type is the signal: a `Map` parameter with a `set`
  in the body is a borrow, and a `ReadonlyMap` is plain. A call statement
  `f(m, x);` becomes `let m := f m x`.

- Should `tolean.json` accept imports without the `.ts` extension, for
  projects that use bundler resolution? Tolean refuses them now because Node
  reads an import as a URL.

  Recommendation: accept them, and follow the project's `tsconfig.json`.
  Import resolution happens outside the parsed program, so no proof sees it.
  Tolean reads `moduleResolution` from the tsconfig when there is one, and a
  field of `tolean.json` otherwise. Under bundler resolution, `./x` resolves
  to `x.ts`, then to `x/index.ts`. Under node16 resolution, `./x.js` resolves
  to `x.ts`, which is the common setup today. The manifest records the
  resolved paths, so the chain stays unambiguous. `.tsx` and anything else
  stay refused.

- Should a comparator that is not one of the two shapes be accepted when the
  project supplies a proof that it is consistent?

  Recommendation: yes, as one case of a general mechanism for obligations.
  Tolean states the obligation, `Consistent cmp`, as a theorem in the output.
  Its tactic proves the two known shapes. When the tactic fails, the project
  may supply the proof in a file beside the output, which the manifest
  records and the build checks for `sorry` and for axioms. The same
  mechanism serves a `@decreases` measure, the counted-loop bound above, and
  keys that must not be `NaN`. The statement always comes from Tolean and the
  project supplies only the proof, so a wrong proof fails the build and a
  wrong statement cannot get in. The obligation may restrict itself to the
  inputs, because a comparator on `number` keys is consistent only without
  `NaN`.

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

  Recommendation: the check on the loop's body, through one predicate that
  the translator and the interpreter share. A binding kind is the faithful
  model, but its cost grows with the whole proof, because `Agree` compares
  kinds and every statement lemma carries them. The check from #63 closes the
  gap in a few lines. One predicate, such as `constRespected`, used both for
  the translator's refusal and for the interpreter's `none`, makes the two
  agree by construction instead of by two parallel checks.
