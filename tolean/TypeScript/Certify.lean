import tolean.TypeScript.Syntax.Parser
import tolean.TypeScript.Certify.Term
import tolean.TypeScript.Spec.Eval
import tolean.TypeScript.Translate

/-!
`tolean certify`: a per-file certificate for a translation.

For one TypeScript file, the certificate holds the parsed program and the
Tolean IR that the translator gives for it as Lean terms, an encoding of each translated Lean
value as a JavaScript value, and one theorem per function:

```
theorem raise_cert (g step) :
    run program "raise" [encGauge g, .int step] = some (encGauge (raise g step))
```

`run` is the interpreter in `Spec/Eval.lean`. When the theorems compile, the
translation of that file is proved: for every input, the translated function
returns what the program returns. This module does not need to be trusted. If
it writes a wrong encoding, a wrong IR or a wrong theorem, Lean refuses the
file.

The theorem follows from `decls_sound` in `Proof/Link.lean`, so it does not
unfold the interpreter. The kernel checks that the parser gives the program
for the source and that the translator gives the IR for the program. Then
a `link` theorem for each function states that the printed definition
computes what `IR/Eval.lean` gives for the IR, and `link_tac` proves it
by unfolding the evaluator.

A loop gets a lemma of its own before the theorem of its function. The lemma
states that the evaluator runs the loop's fold as the printed `List.foldl`,
for every environment whose variables have values of the right types. It
follows from `runFold_foldl`, or from `runFold_forIn` for a loop that a
`break` can end, or from `runFold_forInRet` for one that a `return` can end,
and the theorem of the function uses it as a rewrite rule. To be usable that way, the lemma reads the loop's starting
state, and the other variables that the body reads, back out of the
environment with decoders.

A `number` is a value of the abstract model `JSNumber N`, in the
interpreter as in the translation, so every theorem holds for every `N`.
-/
namespace tolean.TypeScript.Certify

open tolean tolean.TypeScript.Syntax

/-- How the certificate writes the names it uses. A theorem binds the
parameters of its function, and a loop lemma binds locals, so a source name
would hide a Lean name with the same first part. Such a name is written from
the root, as the printer writes the Lean names that the source declares. -/
structure Refs where
  /-- Every identifier in the source. -/
  idents : List String
  /-- The namespace of the certificate. -/
  certNs : String

/-- `short`, or `full` from the root when a source name would hide `short`. -/
def Refs.write (r : Refs) (short full : String) : String :=
  if r.idents.contains ((short.splitOn ".").headD short) then s!"_root_.{full}" else short

/-- The string literal `s` as a `JSString`, as the interpreter gives it. -/
def Refs.jsString (r : Refs) (s : String) : String :=
  s!"({r.write "JSString.ofString" "tolean.TypeScript.JSString.ofString"} {str s})"

/-- Lean code that picks the arm of the string `s`: `if s = "a" then x else
if …`, with `other` when no arm's string is `s`. A `match` cannot test a
`JSString` against `JSString.ofString "a"`, which is not a constructor. `simp`
decides each test with `JSString.ofString_inj`, and `rfl` decides it because
the kernel reduces `ofString` on a literal. -/
def Refs.strArms (r : Refs) (indent : String) (arms : List (String × String)) (other : String) :
    String :=
  String.join (arms.zipIdx.map fun ((t, code), i) =>
    s!"{indent}{if i == 0 then "" else "else "}if s = {r.jsString t} then {code}\n") ++
  s!"{indent}else {other}\n"

/-- A name of `Spec/Eval.lean` or of its lemmas, which the certificate opens. -/
def Refs.eval (r : Refs) (name : String) : String := r.write name s!"tolean.TypeScript.Eval.{name}"

/-- A name that the certificate declares. -/
def Refs.cert (r : Refs) (name : String) : String := r.write name s!"{r.certNs}.{name}"

/-- A name that is already written in full. -/
def Refs.full (r : Refs) (name : String) : String := r.write name name

/-- Every identifier in `source`, at any level, as `Translate.translateFile`
finds them. -/
def sourceIdents (source : String) (target : Edition) : List String :=
  match Syntax.lex source target with
  | .ok tokens => tokens.toList.filterMap fun (t : Syntax.Token) => match t.kind with
    | .ident name => some name
    | _ => none
  | .error _ => []

mutual

/-- How a value of a Lean type of the output becomes a `Val`. -/
def encoderOf (r : Refs) : IR.Ty → Option String
  | .int => some (r.eval "Val.int")
  | .bool => some (r.eval "Val.bool")
  | .string => some (r.eval "Val.str")
  | .option t => do return s!"({r.eval "encNull"} {← encoderOf r t})"
  | .optional t => do return s!"({r.eval "encUndef"} {← encoderOf r t})"
  | .list t => do return s!"({r.eval "encList"} {← encoderOf r t})"
  | .struct ref | .enum ref | .tagged ref => some (r.cert s!"encode{ref.name}")
  | .number => some (r.eval "Val.num")
  | .tuple ts => do return s!"({r.eval "encTuple"} {← elementsEncoder r ts})"
  -- A type parameter has no encoder, so a generic function or interface gets no
  -- certificate yet. Neither has a map or a set, nor a function that can throw.
  | .null | .tag _ | .param _ | .app .. | .map .. | .set _ | .except .. | .error => none

/-- How the elements of a tuple of the types `ts` become a list of `Val`s. -/
def elementsEncoder (r : Refs) : List IR.Ty → Option String
  | [] => none
  | [t] => do return s!"({r.eval "encLast"} {← encoderOf r t})"
  | t :: ts => do return s!"({r.eval "encCons"} {← encoderOf r t} {← elementsEncoder r ts})"

end

mutual

/-- How a variable's value becomes a Lean value of type `t` again. -/
def decoderOf (r : Refs) : IR.Ty → Option String
  | .int => some (r.eval "decInt")
  | .bool => some (r.eval "decBool")
  | .string => some (r.eval "decStr")
  | .option t => do return s!"({r.eval "decNull"} {← decoderOf r t})"
  | .optional t => do return s!"({r.eval "decUndef"} {← decoderOf r t})"
  | .list t => do return s!"({r.eval "decList"} {← decoderOf r t})"
  | .struct ref | .enum ref | .tagged ref => some (r.cert s!"decode{ref.name}")
  | .number => some (r.eval "decNum")
  | .tuple ts => do return s!"({r.eval "decTuple"} {← elementsDecoder r ts})"
  | .null | .tag _ | .param _ | .app .. | .map .. | .set _ | .except .. | .error => none

/-- How a list of `Val`s becomes the elements of a tuple of the types `ts`. -/
def elementsDecoder (r : Refs) : List IR.Ty → Option String
  | [] => none
  | [t] => do return s!"({r.eval "decLast"} {← decoderOf r t})"
  | t :: ts => do return s!"({r.eval "decCons"} {← decoderOf r t} {← elementsDecoder r ts})"

end

/-- The constructor of `Val` for a value of the primitive type `t`. -/
def valPattern : IR.Ty → Option String
  | .int => some ".int"
  | .bool => some ".bool"
  | .string => some ".str"
  | .number => some ".num"
  | _ => none

/-- The statements of a function body, with nested ones. -/
partial def stmtsOf : Stmt → List Stmt
  | .block _ body => .block default body :: body.flatMap stmtsOf
  | .ifStmt s t a b => .ifStmt s t a b :: stmtsOf a ++ ((b.map stmtsOf).getD [])
  | .forOfStmt s k n i b => .forOfStmt s k n i b :: stmtsOf b
  | .forStmt s i t u b => .forStmt s i t u b :: stmtsOf b
  | .whileStmt s t b => .whileStmt s t b :: stmtsOf b
  | .switchStmt s d cs => .switchStmt s d cs :: cs.flatMap fun (_, body) => body.flatMap stmtsOf
  | s => [s]

partial def exprCalls : Expr → List String
  | .call _ (.ident _ f) args => f :: args.flatMap exprCalls
  | .call _ c args => exprCalls c ++ args.flatMap exprCalls
  | .paren _ e | .member _ e _ | .optMember _ e _ | .unary _ _ e | .prefix _ _ e | .postfix _ _ e
  | .asConst _ e | .satisfies _ e _ =>
    exprCalls e
  | .index _ a b | .binary _ _ a b | .assign _ _ a b => exprCalls a ++ exprCalls b
  | .cond _ a b c => exprCalls a ++ exprCalls b ++ exprCalls c
  | .array _ es => es.flatMap exprCalls
  | .object _ ps => ps.flatMap fun | .keyValue _ _ v => exprCalls v | _ => []
  | .arrow _ _ _ body => exprCalls body
  | _ => []

/-- The text of each number literal in `e`. -/
partial def exprNumbers : Expr → List String
  | .number _ t => [t]
  | .call _ c args => exprNumbers c ++ args.flatMap exprNumbers
  | .paren _ e | .member _ e _ | .optMember _ e _ | .unary _ _ e | .prefix _ _ e | .postfix _ _ e
  | .asConst _ e | .satisfies _ e _ =>
    exprNumbers e
  | .index _ a b | .binary _ _ a b | .assign _ _ a b => exprNumbers a ++ exprNumbers b
  | .cond _ a b c => exprNumbers a ++ exprNumbers b ++ exprNumbers c
  | .array _ es => es.flatMap exprNumbers
  | .object _ ps => ps.flatMap fun | .keyValue _ _ v => exprNumbers v | _ => []
  | .arrow _ _ _ body => exprNumbers body
  | _ => []

def stmtNumbers : Stmt → List String
  | .varDecl _ d => (d.init.map exprNumbers).getD []
  | .exprStmt _ e | .ifStmt _ e _ _ | .whileStmt _ e _ | .forOfStmt _ _ _ e _ => exprNumbers e
  | .returnStmt _ e => (e.map exprNumbers).getD []
  | .forStmt _ i t u _ =>
    (((i.bind (·.init)).map exprNumbers).getD []) ++ ((t.map exprNumbers).getD []) ++ ((u.map exprNumbers).getD [])
  | _ => []

def stmtCalls : Stmt → List String
  | .varDecl _ d => (d.init.map exprCalls).getD []
  | .exprStmt _ e | .ifStmt _ e _ _ | .whileStmt _ e _ | .forOfStmt _ _ _ e _ => exprCalls e
  | .returnStmt _ e => (e.map exprCalls).getD []
  | .forStmt _ i t u _ =>
    (((i.bind (·.init)).map exprCalls).getD []) ++ ((t.map exprCalls).getD []) ++ ((u.map exprCalls).getD [])
  | .switchStmt _ d cs => exprCalls d ++ cs.flatMap fun (t, _) => (t.map exprCalls).getD []
  | _ => []

def functionsOf (m : Module) : List (String × List Param × Option TypeExpr × Stmt) :=
  m.decls.filterMap fun
    | .function _ _ n _ ps r b => some (n, ps, r, b)
    | _ => none

/-- The functions that get a certificate: all of them. -/
def certifiable (m : Module) : List String := (functionsOf m).map (·.1)

/-- How deep the calls of `calls`, and the calls in their bodies, nest: the
fuel that the interpreter needs to run them. `certify` refuses a function
that calls itself, so the depth is finite. -/
partial def callsDepth (m : Module) (calls : List String) : Nat :=
  let rec go (fuel : Nat) (calls : List String) : Nat :=
    match fuel with
    | 0 => 0
    | fuel + 1 =>
      calls.foldl (init := 0) fun acc f =>
        match (functionsOf m).find? (·.1 == f) with
        | some (_, _, _, body) => max acc (go fuel ((stmtsOf body).flatMap stmtCalls) + 1)
        | none => acc
  go ((functionsOf m).length + 1) calls

/-- How deep the calls in `s` nest. -/
def callDepth (m : Module) (s : Stmt) : Nat := callsDepth m ((stmtsOf s).flatMap stmtCalls)

/-- `e` and every expression inside it. -/
partial def subExprs (e : Expr) : List Expr :=
  e :: match e with
    | .call _ c args => subExprs c ++ args.flatMap subExprs
    | .paren _ e | .member _ e _ | .optMember _ e _ | .unary _ _ e | .prefix _ _ e | .postfix _ _ e
    | .arrow _ _ _ e => subExprs e
    | .index _ a b | .binary _ _ a b | .assign _ _ a b => subExprs a ++ subExprs b
    | .cond _ a b c => subExprs a ++ subExprs b ++ subExprs c
    | .array _ es => es.flatMap subExprs
    | .object _ ps => ps.flatMap fun | .keyValue _ _ v => subExprs v | _ => []
    | _ => []

/-- The expressions that a statement holds, outside its nested statements. -/
def stmtExprs : Stmt → List Expr
  | .varDecl _ d => d.init.toList
  | .exprStmt _ e | .ifStmt _ e _ _ | .whileStmt _ e _ | .forOfStmt _ _ _ e _ => [e]
  | .returnStmt _ e => e.toList
  | .switchStmt _ d cs => d :: cs.filterMap (·.1)
  | _ => []

/-- The call at `span` in `s`, such as `xs.map(x => e)`. -/
def callAt (s : Stmt) (span : Span) : Option Expr :=
  ((stmtsOf s).flatMap stmtExprs).findSome? fun e =>
    (subExprs e).find? fun
      | .call sp _ _ => sp == span
      | _ => false

/-- What a callback is for: a `List` function such as `List.map`, or
`List.foldl`, whose function also binds the value so far to `acc`. -/
inductive CallbackKind where
  | list (method : IR.ListMethod)
  | fold (acc : String)

/-- A call of a `List` function with a callback: what it is for, the parameter,
its type, the body and what a certificate needs to know about it. -/
abbrev Callback := CallbackKind × String × IR.Ty × IR.Expr × IR.CallbackInfo IR.TyExt

mutual

/-- The callbacks in `e`, inner ones first, in the order of the source. -/
partial def exprCallbacks : IR.Expr → List Callback
  | .listMethod method items param elem body info =>
    exprCallbacks items ++ exprCallbacks body ++ [(.list method, param, elem, body, info)]
  | .listFold items init acc param elem body info =>
    exprCallbacks items ++ exprCallbacks init ++ exprCallbacks body ++ [(.fold acc, param, elem, body, info)]
  | .field a _ _ | .propNot a | .not a | .neg a | .isNone a | .isSome a | .decide a | .push _ a
  | .update _ _ a | .inject _ _ a | .ascribe a _ => exprCallbacks a
  | .ite a b c => exprCallbacks a ++ exprCallbacks b ++ exprCallbacks c
  | .matchNull _ a b | .coalesce a b _ | .intOp _ a b | .order _ a b | .division _ a b
  | .eq a b | .ne a b | .propAnd a b | .propOr a b | .and a b | .or a b =>
    exprCallbacks a ++ exprCallbacks b
  | .call _ args | .list args _ | .ext _ args => args.flatMap exprCallbacks
  | .struct fields _ _ => fields.flatMap (exprCallbacks ·.2)
  | .structUpdate base fields => exprCallbacks base ++ fields.flatMap (exprCallbacks ·.2)
  | .tuple es => es.flatMap exprCallbacks
  | .proj e _ _ => exprCallbacks e
  | .int _ | .none | .bool _ | .string _ | .var _ | .enumCase .. | .tagValue _ => []

/-- The names that `e` reads. -/
partial def exprNames : IR.Expr → List String
  | .var n => [n]
  | .listMethod _ items _ _ body _ => exprNames items ++ exprNames body
  | .listFold items init _ _ _ body _ => exprNames items ++ exprNames init ++ exprNames body
  | .push n a | .update _ n a => n :: exprNames a
  | .matchNull n a b => n :: exprNames a ++ exprNames b
  | .field a _ _ | .propNot a | .not a | .neg a | .isNone a | .isSome a | .decide a
  | .inject _ _ a | .ascribe a _ => exprNames a
  | .ite a b c => exprNames a ++ exprNames b ++ exprNames c
  | .coalesce a b _ | .intOp _ a b | .order _ a b | .division _ a b
  | .eq a b | .ne a b | .propAnd a b | .propOr a b | .and a b | .or a b =>
    exprNames a ++ exprNames b
  | .call _ args | .list args _ | .ext _ args => args.flatMap exprNames
  | .struct fields _ _ => fields.flatMap (exprNames ·.2)
  | .structUpdate base fields => exprNames base ++ fields.flatMap (exprNames ·.2)
  | .tuple es => es.flatMap exprNames
  | .proj e _ _ => exprNames e
  | .int _ | .none | .bool _ | .string _ | .enumCase .. | .tagValue _ => []

/-- The callbacks in a body, inner ones first, in the order of the source. -/
partial def bodyCallbacks : IR.Body → List Callback
  | .value e => exprCallbacks e
  | .state _ | .yield .. | .done .. => []
  | .exit e _ => exprCallbacks e
  | .let _ e rest => exprCallbacks e ++ bodyCallbacks rest
  | .letArray _ _ elems rest => elems.flatMap exprCallbacks ++ bodyCallbacks rest
  | .ite c a b => exprCallbacks c ++ bodyCallbacks a ++ bodyCallbacks b
  | .matchNull _ _ a b | .matchTag _ _ _ _ _ a b | .letState _ a b => bodyCallbacks a ++ bodyCallbacks b
  | .fold _ _ body items rest _ => exprCallbacks items ++ bodyCallbacks body ++ bodyCallbacks rest
  | .throw e => exprCallbacks e
  | .bind _ _ args rest => args.flatMap exprCallbacks ++ bodyCallbacks rest

end

/-- The body of the `for…of` statement at `span`. -/
def loopBody (s : Stmt) (span : Span) : Option Stmt :=
  (stmtsOf s).findSome? fun
    | .forOfStmt sp _ _ _ body => if sp == span then some body else none
    | _ => none

/-- The tactics that split the variable `name` of type `t`, so that each case
sees a known value: a nullable value on `none` and `some`, a literal union on
its constructors, and a value of an interface of the file into its fields,
each of which is split in turn. So
`p.inner.x ?? 1n` sees a known value for `x`, and so does a field of a
nullable interface. An interface names only the interfaces before it, so
`fuel`, the number of declarations, bounds how deep the fields nest. -/
def splitSteps (decls : List IR.Decl) : Nat → String → IR.Ty → List String
  | 0, _, _ => []
  | fuel + 1, name, .option t | fuel + 1, name, .optional t =>
    s!"rcases {name} with _ | {name}" :: splitSteps decls fuel name t
  | _ + 1, name, .enum _ => [s!"cases {name}"]
  | fuel + 1, name, .struct ref =>
    let fields := decls.findSome? fun
      | .struct n _ fields => if n == ref.name then some fields else none
      | _ => none
    match fields with
    | some fields =>
      -- The structure leaves its tag fields out.
      let fields := fields.filter fun (_, ft) => !(ft matches .tag _)
      let inner := fields.flatMap fun (f, ft) => splitSteps decls fuel s!"{name}_{f}" ft
      if inner.isEmpty then []
      else s!"rcases {name} with ⟨{", ".intercalate (fields.map fun (f, _) => s!"{name}_{f}")}⟩" :: inner
    | none => []
  | fuel + 1, name, .tuple ts =>
    let parts := (List.range ts.length).map (s!"{name}_{·}")
    let inner := (parts.zip ts).flatMap fun (n, t) => splitSteps decls fuel n t
    if inner.isEmpty then []
    else s!"rcases {name} with ⟨{", ".intercalate parts}⟩" :: inner
  | fuel + 1, name, .tagged ref =>
    let members := decls.findSome? fun
      | .tagged n _ members => if n == ref.name then some members else none
      | _ => none
    match members with
    | some members =>
      s!"rcases {name} with {" | ".intercalate (members.map fun _ => name)}" ::
        members.flatMap fun (_, member) => splitSteps decls fuel name member
    | none => []
  | _ + 1, _, _ => []

/-- The splits of `vars`, as a prefix of the tactic that follows them. Each
split runs under `try`, because the `none` case of a nullable value has no
fields to split. -/
def casesOn (decls : List IR.Decl) (vars : List (String × IR.Ty)) : String :=
  String.join ((vars.flatMap fun (n, t) => splitSteps decls (decls.length + 1) n t).map
    (s!"(try {·}) <;> "))

/-- The loops of a body, inner ones first, in the order of the source. -/
partial def loopsOf : IR.Body → List (List String × String × IR.Body × IR.LoopInfo)
  | .value _ | .state _ | .yield .. | .done .. | .exit .. => []
  | .let _ _ rest | .letArray _ _ _ rest => loopsOf rest
  | .ite _ a b | .matchNull _ _ a b | .matchTag _ _ _ _ _ a b => loopsOf a ++ loopsOf b
  | .letState _ branch rest => loopsOf branch ++ loopsOf rest
  | .fold names element body _ rest info => loopsOf body ++ [(names, element, body, info)] ++ loopsOf rest
  | .throw _ => []
  | .bind _ _ _ rest => loopsOf rest

/-- `s`, the state of a loop with the locals `names`, as the path to one of
them: `s`, `s.1`, `s.2.1`, and so on. -/
def project (s : String) (count index : Nat) : String :=
  if count == 1 then s
  else
    let seconds := String.join (List.replicate index ".2")
    if index + 1 == count then s!"{s}{seconds}" else s!"{s}{seconds}.1"

/-- A value as a Lean term. The derived `Repr` writes each constructor by its
full name, so Lean reads the text back as the same value. If it did not, the
kernel's check in the certificate would fail, so this need not be trusted. -/
def term {α : Type} [Repr α] (x : α) : String := (repr x).pretty 100

/-- The certificate file for `source`, translated as the Lean module `leanModule`
with namespace `transNs`. -/
def certify (file source leanModule transNs certNs : String) (target : Edition := .default) :
    Except String String := do
  if let .ok m := Syntax.parse source target then
    if m.decls.any (· matches .import ..) then
      throw s!"{file}: a file with imports has no certificate yet"
  -- The certificate's program is the file "", so the tree names the file's
  -- own declarations under "".
  let (m, names, decls) ← (Translate.translateTree "" source target).mapError (file ++ ·)
  let r : Refs := { idents := sourceIdents source target, certNs }
  -- A loop lemma's step function binds the loop's locals, so the printer
  -- writes the translation's names as `Refs` does.
  let names := { names with namespacePrefix := r.full transNs ++ "." }
  let fns := certifiable m
  if fns.isEmpty then throw s!"{file}: there is no function to certify"
  -- A theorem runs the interpreter with the fuel that the depth of the calls
  -- needs, and a function that calls itself has no such depth.
  for d in decls do
    if let .function name _ _ body := d then
      if body.calls ⟨"", name⟩ then throw s!"{file}: the recursive function {name} has no certificate yet"
  -- A theorem states that the interpreter gives a value for every input, but
  -- it gives none for a counted loop whose counter would pass
  -- `Number.MAX_SAFE_INTEGER`.
  if m.decls.any fun d => match d with
      | .function _ _ _ _ _ _ body => (stmtsOf body).any (· matches .forStmt ..)
      | _ => false then
    throw s!"{file}: a counted loop has no certificate yet"
  let nv := names.typeParam
  -- Every theorem is about every number model.
  let generic := s!"\{{nv} : Type} [tolean.TypeScript.JSNumber {nv}]"
  -- A generic translated definition takes the model by name, as the
  -- translation's own calls do.
  let callN := if names.generic then s!" ({nv} := {nv})" else ""
  let structTy (name : String) : String := (IR.Ty.struct ⟨"", name⟩ : IR.Ty).print names
  let mut encs : Array String := #[]
  let mut lemmaNames : Array String :=
    #["encList", "decInt", "decBool", "decStr", "decNum"].map r.eval
  -- The codecs of the declarations, in their order: a type names only the
  -- types before it, so each codec comes after the codecs it uses.
  for d in decls do
    -- A literal union: each constructor is its string.
    if let .enum name members := d then
      let ty := (IR.Ty.enum ⟨"", name⟩ : IR.Ty).print names
      let ctor (m : String) : String := (IR.Expr.enumCase ⟨"", name⟩ m : IR.Expr).print names
      let first := members.head?.getD ""
      encs := encs.push <|
        s!"def encode{name} {generic} : {ty} → Val {nv}\n" ++
        "\n".intercalate (members.map fun m => s!"  | {ctor m} => Val.str {r.jsString m}")
      encs := encs.push <|
        s!"def decode{name} {generic} : Option (Val {nv}) → {ty}\n" ++
        "  | some (.str s) =>\n" ++
        r.strArms "    " (members.map fun m => (m, ctor m)) (ctor first) ++
        s!"  | _ => {ctor first}"
      encs := encs.push <|
        s!"@[simp] theorem decode{name}_encode{name} {generic} (x : {ty}) : decode{name} (some (encode{name} ({nv} := {nv}) x)) = x := by\n" ++
        s!"  cases x <;> rfl"
      encs := encs.push <|
        s!"@[simp] theorem encode{name}_ne_null {generic} (x : {ty}) : encode{name} ({nv} := {nv}) x ≠ Val.null := by\n" ++
        s!"  cases x <;> simp [encode{name}]"
      encs := encs.push <|
        s!"@[simp] theorem encode{name}_ne_undefined {generic} (x : {ty}) : encode{name} ({nv} := {nv}) x ≠ Val.undefined := by\n" ++
        s!"  cases x <;> simp [encode{name}]"
      encs := encs.push <|
        s!"@[simp] theorem decList_decode{name} {generic} (xs : List {ty}) : decList decode{name} (some (Val.list (List.map (encode{name} ({nv} := {nv})) xs))) = xs :=\n" ++
        s!"  decList_list _ _ decode{name}_encode{name} xs"
      -- The same for an array of nullable values, which `simp` would
      -- otherwise reach only through side conditions that it cannot discharge
      -- once it unfolds the encoder.
      encs := encs.push <|
        s!"@[simp] theorem decList_decNull_decode{name} {generic} (xs : List (Option {ty})) : decList (decNull decode{name}) (some (Val.list (List.map (encNull (encode{name} ({nv} := {nv}))) xs))) = xs :=\n" ++
        s!"  decList_list_null _ _ decode{name}_encode{name} encode{name}_ne_null xs"
      -- `simp` keeps the encoder and the decoder folded and uses these, so
      -- that `decode{name}_encode{name}` still applies where a value is not
      -- split.
      for (m, i) in members.zipIdx do
        encs := encs.push <|
          s!"@[simp] theorem encode{name}_{i} {generic} : encode{name} ({nv} := {nv}) {ctor m} = Val.str {r.jsString m} := rfl"
        encs := encs.push <|
          s!"@[simp] theorem decode{name}_{i} {generic} : decode{name} ({nv} := {nv}) (some (Val.str {r.jsString m})) = {ctor m} := rfl"
        -- `xs.includes(x)` on the union: the value of `x` is the string of
        -- the constructor, which is the same as an element's encoding only
        -- when the element is that constructor.
        encs := encs.push <|
          s!"@[simp] theorem includes{name}_{i} {generic} (xs : List {ty}) : " ++
          s!"{r.eval "includesVal"} ({nv} := {nv}) (Val.str {r.jsString m}) (List.map encode{name} xs) = " ++
          s!"some (decide ({ctor m} ∈ xs)) :=\n" ++
          s!"  tolean.TypeScript.Proof.includesVal_enc _ _ _ (fun y => by cases y <;> " ++
          s!"simp [encode{name}, {r.eval "sameValueZero"}, {r.eval "strictEq"}]) xs"
    -- An interface.
    if let .struct name typeParams allFields := d then
      unless typeParams.isEmpty do throw s!"{file}: the generic interface {name} has no certificate yet"
      -- The encoder of an interface that refers to itself would be recursive.
      if allFields.any (fun (_, t) => t.refs.any (·.name == name)) then
        throw s!"{file}: the recursive interface {name} has no certificate yet"
      -- An optional field is a key only when it holds a value, as in an
      -- object literal that leaves it out.
      let parts ← allFields.mapM fun (f, t) => do
        if let .tag v := t then return (s!"({str f}, Val.str {r.jsString v})", false)
        if let .optional u := t then
          let some e := encoderOf r u | throw s!"{file}: cannot encode the field {name}.{f}"
          return (s!"({r.eval "encField"} {str f} {e} x.{f})", true)
        let some e := encoderOf r t | throw s!"{file}: cannot encode the field {name}.{f}"
        return (s!"({str f}, {e} x.{f})", false)
      let hasOptional := parts.any (·.2)
      let objList := if hasOptional then
          " ++ ".intercalate (parts.map fun (p, opt) => if opt then p else s!"[{p}]")
        else list (parts.map (·.1))
      -- The structure has no tag fields, so the decoder reads none.
      let fields := allFields.filter fun (_, t) => !(t matches .tag _)
      let decs ← fields.mapM fun (f, t) => do
        let some dec := decoderOf r t | throw s!"{file}: cannot decode the field {name}.{f}"
        return (f, dec)
      let some_ := ", ".intercalate (decs.map fun (f, dec) => s!"{f} := {dec} (fs.lookup {str f})")
      let none_ := ", ".intercalate (decs.map fun (f, dec) => s!"{f} := {dec} (none : Option (Val {nv}))")
      encs := encs.push s!"def encode{name} {generic} (x : {structTy name}) : Val {nv} := Val.obj {if hasOptional then s!"({objList})" else objList}"
      encs := encs.push <|
        s!"def decode{name} {generic} : Option (Val {nv}) → {structTy name}\n" ++
        s!"  | some (.obj fs) => \{ {some_} }\n" ++
        s!"  | _ => \{ {none_} }"
      -- With optional fields, the proof splits each into its two cases.
      let optionalFields := fields.filterMap fun (f, t) => if t matches .optional _ then some f else none
      let splitOptional := if optionalFields.isEmpty then "cases x"
        else s!"obtain ⟨{", ".intercalate (fields.map fun (f, _) => s!"x_{f}")}⟩ := x\n  " ++
          String.join (optionalFields.map fun f => s!"cases x_{f} <;> ")
      encs := encs.push <|
        s!"@[simp] theorem decode{name}_encode{name} {generic} (x : {structTy name}) : decode{name} (some (encode{name} ({nv} := {nv}) x)) = x := by\n" ++
        s!"  {splitOptional}{if optionalFields.isEmpty then "; " else ""}simp [decode{name}, encode{name}, List.lookup, encList]"
      encs := encs.push <|
        s!"@[simp] theorem encode{name}_ne_null {generic} (x : {structTy name}) : encode{name} ({nv} := {nv}) x ≠ Val.null := by\n" ++
        s!"  simp [encode{name}]"
      encs := encs.push <|
        s!"@[simp] theorem encode{name}_ne_undefined {generic} (x : {structTy name}) : encode{name} ({nv} := {nv}) x ≠ Val.undefined := by\n" ++
        s!"  simp [encode{name}]"
      -- An array of the interface, as a loop over it reads its variable back.
      -- `simp` cannot find this from `decList_list` when the fields nest, so
      -- the certificate states it.
      encs := encs.push <|
        s!"@[simp] theorem decList_decode{name} {generic} (xs : List {structTy name}) : decList decode{name} (some (Val.list (List.map (encode{name} ({nv} := {nv})) xs))) = xs :=\n" ++
        s!"  decList_list _ _ decode{name}_encode{name} xs"
      -- The same for an array of nullable values, which `simp` would
      -- otherwise reach only through side conditions that it cannot discharge
      -- once it unfolds the encoder.
      encs := encs.push <|
        s!"@[simp] theorem decList_decNull_decode{name} {generic} (xs : List (Option {structTy name})) : decList (decNull decode{name}) (some (Val.list (List.map (encNull (encode{name} ({nv} := {nv}))) xs))) = xs :=\n" ++
        s!"  decList_list_null _ _ decode{name}_encode{name} encode{name}_ne_null xs"
      lemmaNames := lemmaNames ++ #[r.cert s!"encode{name}", r.cert s!"decode{name}"]
    -- A union of primitive types: each member is its value, and the decoder
    -- reads the kind of the value to pick the member.
    if let .tagged name none members := d then
      let ty := (IR.Ty.tagged ⟨"", name⟩ : IR.Ty).print names
      let ctor (t : String) : String := s!"{(names.ref ⟨"", name⟩).1}.{IR.memberName t}"
      let some (firstTag, firstTy) := members.head? | throw s!"{file}: the union {name} has no members"
      let some firstDec := decoderOf r firstTy | throw s!"{file}: cannot decode the union {name}"
      let codecs ← members.mapM fun (t, mt) => do
        let (some enc, some pat) := (encoderOf r mt, valPattern mt)
          | throw s!"{file}: cannot encode the member {t} of {name}"
        return (t, enc, pat)
      encs := encs.push <|
        s!"def encode{name} {generic} : {ty} → Val {nv}\n" ++
        "\n".intercalate (codecs.map fun (t, enc, _) => s!"  | {ctor t} v => {enc} v")
      encs := encs.push <|
        s!"def decode{name} {generic} : Option (Val {nv}) → {ty}\n" ++
        String.join (codecs.map fun (t, _, pat) => s!"  | some ({pat} v) => {ctor t} v\n") ++
        s!"  | _ => {ctor firstTag} ({firstDec} (none : Option (Val {nv})))"
      encs := encs.push <|
        s!"@[simp] theorem decode{name}_encode{name} {generic} (x : {ty}) : decode{name} (some (encode{name} ({nv} := {nv}) x)) = x := by\n" ++
        s!"  cases x <;> rfl"
      encs := encs.push <|
        s!"@[simp] theorem encode{name}_ne_null {generic} (x : {ty}) : encode{name} ({nv} := {nv}) x ≠ Val.null := by\n" ++
        s!"  cases x <;> simp [encode{name}]"
      encs := encs.push <|
        s!"@[simp] theorem decList_decode{name} {generic} (xs : List {ty}) : decList decode{name} (some (Val.list (List.map (encode{name} ({nv} := {nv})) xs))) = xs :=\n" ++
        s!"  decList_list _ _ decode{name}_encode{name} xs"
      lemmaNames := lemmaNames ++ #[r.cert s!"encode{name}", r.cert s!"decode{name}"]
    -- A tagged union of structures: each member is the object of its
    -- structure, which holds the tag, and the decoder reads the tag to pick
    -- the member.
    if let .tagged name (some field) members := d then
      let ty := (IR.Ty.tagged ⟨"", name⟩ : IR.Ty).print names
      let ctor (t : String) : String := s!"{(names.ref ⟨"", name⟩).1}.{IR.memberName t}"
      let members := members.filterMap fun
        | (t, .struct m) => some (t, m)
        | _ => none
      let some (firstTag, firstRef) := members.head? | throw s!"{file}: the union {name} has no members"
      encs := encs.push <|
        s!"def encode{name} {generic} : {ty} → Val {nv}\n" ++
        "\n".intercalate (members.map fun (t, m) => s!"  | {ctor t} v => encode{m.name} v")
      encs := encs.push <|
        s!"def decode{name} {generic} : Option (Val {nv}) → {ty}\n" ++
        s!"  | some (.obj fs) =>\n    match fs.lookup {str field} with\n" ++
        "    | some (.str s) =>\n" ++
        r.strArms "      "
          (members.map fun (t, m) => (t, s!"{ctor t} (decode{m.name} ({nv} := {nv}) (some (.obj fs)))"))
          s!"{ctor firstTag} (decode{firstRef.name} ({nv} := {nv}) none)" ++
        s!"    | _ => {ctor firstTag} (decode{firstRef.name} ({nv} := {nv}) none)\n" ++
        s!"  | _ => {ctor firstTag} (decode{firstRef.name} ({nv} := {nv}) none)"
      let memberDefs := ", ".intercalate (members.flatMap fun (_, m) => [s!"encode{m.name}", s!"decode{m.name}"])
      -- One arm for each member. As for an interface, the proof splits each
      -- optional field of the member's structure into its two cases.
      let memberFields (ref : DeclRef) : List (String × IR.Ty) :=
        ((decls.findSome? fun
          | .struct n _ fs => if n == ref.name then some fs else none
          | _ => none).getD []).filter fun (_, t) => !(t matches .tag _)
      let arms := members.map fun (t, m) =>
        let fs := memberFields m
        let opts := fs.filterMap fun (f, t) => if t matches .optional _ then some f else none
        let split := if opts.isEmpty then "cases v <;> "
          else s!"obtain ⟨{", ".intercalate (fs.map fun (f, _) => s!"v_{f}")}⟩ := v\n    " ++
            String.join (opts.map fun f => s!"cases v_{f} <;> ")
        s!"  | {IR.memberName t} v =>\n    {split}simp [decode{name}, encode{name}, {memberDefs}, List.lookup, encList]"
      encs := encs.push <|
        s!"@[simp] theorem decode{name}_encode{name} {generic} (x : {ty}) : decode{name} (some (encode{name} ({nv} := {nv}) x)) = x := by\n" ++
        "  cases x with\n" ++ "\n".intercalate arms
      encs := encs.push <|
        s!"@[simp] theorem encode{name}_ne_null {generic} (x : {ty}) : encode{name} ({nv} := {nv}) x ≠ Val.null := by\n" ++
        s!"  cases x <;> simp [encode{name}, {memberDefs}]"
      encs := encs.push <|
        s!"@[simp] theorem encode{name}_ne_undefined {generic} (x : {ty}) : encode{name} ({nv} := {nv}) x ≠ Val.undefined := by\n" ++
        s!"  cases x <;> simp [encode{name}, {memberDefs}]"
      encs := encs.push <|
        s!"@[simp] theorem decList_decode{name} {generic} (xs : List {ty}) : decList decode{name} (some (Val.list (List.map (encode{name} ({nv} := {nv})) xs))) = xs :=\n" ++
        s!"  decList_list _ _ decode{name}_encode{name} xs"
      -- The same for an array of nullable values, which `simp` would
      -- otherwise reach only through side conditions that it cannot discharge
      -- once it unfolds the encoder.
      encs := encs.push <|
        s!"@[simp] theorem decList_decNull_decode{name} {generic} (xs : List (Option {ty})) : decList (decNull decode{name}) (some (Val.list (List.map (encNull (encode{name} ({nv} := {nv}))) xs))) = xs :=\n" ++
        s!"  decList_list_null _ _ decode{name}_encode{name} encode{name}_ne_null xs"
      lemmaNames := lemmaNames ++ #[r.cert s!"encode{name}", r.cert s!"decode{name}"]
  let defs := (functionsOf m).map fun f => r.full s!"{transNs}.{f.1}"
  let outputFs := s!"({r.full "tolean.TypeScript.IR.functionsOf"} [(\"\", {r.cert "decls"})])"
  let envLemmas := ["Env.set_cons", "Env.lookup_cons", "Env.lookup_set_same", "Env.lookup_set_ne",
    "Env.set_set", "Env.length_set"].map r.eval
  let mut loopLemmas : Array String := #[]
  let mut thms : Array String := #[]
  for d in m.decls do
    let .function _ _ name _ params _ syntaxBody := d | continue
    unless fns.contains name do continue
    let some (.function _ outParams outRet outBody) := decls.find? fun
        | .function n .. => n == name
        | _ => false
      | throw s!"{file}: no translation of {name}"
    -- A callback gets a lemma before the loops, because a loop's body can
    -- hold one, and before the callbacks that hold it.
    let mut cbIndex := 0
    for (method, param, elem, cbBody, info) in bodyCallbacks outBody do
      cbIndex := cbIndex + 1
      let lemmaName := s!"{name}_cb{cbIndex}"
      let some encX := encoderOf r elem
        | throw s!"{file}: cannot encode the elements of a callback in {name}"
      let some encY := encoderOf r info.result
        | throw s!"{file}: cannot encode the value of a callback in {name}"
      -- The lemma reads back only the locals that the body reads.
      let reads := exprNames cbBody
      let scope := info.scope.filter fun (n, _) => reads.contains n
      let coded ← scope.mapM fun (n, t) => do
        let (some e, some dec) := (encoderOf r t, decoderOf r t)
          | throw s!"{file}: cannot encode the variable {n} in {name}"
        return (n, e, dec)
      let decode (n : String) : String :=
        match coded.find? (·.1 == n) with
        | some (_, _, dec) => s!"({dec} (ρ.lookup {str n}))"
        | none => "default"
      -- The callback's function binds the locals that its body reads, as a
      -- loop's step does, and the lemma reads them back out of `ρ`.
      let captured := if scope.isEmpty then "" else
        s!"fun {" ".intercalate (scope.map fun (n, t) => s!"({n} : {t.print names})")} => "
      -- The function of `List.mapIdx` binds the index first, as a `Nat`, and
      -- then as the number that the body reads, as the printer writes it.
      let binders := match method with
        | .fold acc => s!"fun ({acc} : {info.result.print names}) ({param} : {elem.print names}) => "
        | .list (.mapIdx index) =>
          s!"fun ({index} : {tolean.IR.leanName names "Nat"}) ({param} : {elem.print names}) => " ++
            s!"let {index} := {tolean.IR.PrintTy.indexValue (T := IR.TyExt) names index}; "
        | _ => s!"fun ({param} : {elem.print names}) => "
      let fn := s!"(({captured}{binders}({cbBody.print names} : {info.result.print names}))" ++
        String.join (scope.map fun (n, _) => s!" {decode n}") ++ ")"
      -- A body with calls needs the fuel of their depth, as a loop's does.
      let depth := match callAt syntaxBody info.span with
        | some (.call _ _ (.arrow _ _ _ arrowBody :: _)) => callsDepth m (exprCalls arrowBody)
        | _ => 0
      let fuel := if depth == 0 then "fuel" else s!"(fuel + {depth})"
      let hfs := if depth == 0 then "" else s!" (hfs : fs = {outputFs})"
      let substHfs := if depth == 0 then "" else "  subst hfs\n"
      let hfsName := if depth == 0 then [] else [r.cert "decls"]
      let inv := " ∧ ".intercalate (coded.map fun (n, e, dec) =>
        s!"ρ.lookup {str n} = some ({e} ({dec} (ρ.lookup {str n})))")
      let hI := if coded.isEmpty then "" else s!" (hI : {inv})"
      let hypNames := (List.range coded.length).map (s!"h{·}")
      let unpack := if coded.isEmpty then "" else
        -- Here `obtain` would give names that the tactics after it cannot
        -- see, so each part of `hI` gets a `have`.
        String.join (hypNames.zipIdx.map fun (h, i) => s!"  have {h} := hI{project "" coded.length i}\n") ++
          "  try simp only []\n" ++
          String.join (coded.zipIdx.map fun ((n, _, dec), i) =>
            s!"  generalize {dec} (ρ.lookup {str n}) = v{i} at h{i} ⊢\n")
      let simpSet := ", ".intercalate (hfsName ++ envLemmas ++ lemmaNames.toList ++ loopLemmas.toList ++ defs ++ hypNames)
      let itemsTy := (IR.Ty.list elem).print names
      -- A callback of `reduce`: the lemma holds for every value so far `a`,
      -- which the body reads under the name of the first parameter. It holds
      -- for every initial value `v` that decodes and encodes back to itself,
      -- because the proof of the function sees the initial value with its
      -- encoding unfolded, such as `Val.list (List.map Val.int init)`.
      if let .fold acc := method then
        let some decY := decoderOf r info.result
          | throw s!"{file}: cannot decode the value of a callback in {name}"
        let vars := ("a", info.result) :: ("x", elem) :: scope.zipIdx.map fun ((_, t), i) => (s!"v{i}", t)
        loopLemmas := loopLemmas.push (r.cert lemmaName)
        thms := thms.push <|
          s!"theorem {lemmaName} {generic} (fs : List (tolean.DeclRef × List String × tolean.TypeScript.IR.Body)){hfs}\n" ++
          s!"    (fuel : Nat) (ρ : Env {nv}){hI} (items : {itemsTy}) (v : Val {nv})\n" ++
          s!"    (hv : {encY} ({decY} (some v)) = v) :\n" ++
          s!"    tolean.TypeScript.IR.Expr.evalReduce fs {fuel} ρ {str acc} {str param} ({term cbBody})\n" ++
          s!"      v (List.map {encX} items) = some ({encY} (List.foldl {fn} ({decY} (some v)) items)) := by\n" ++
          s!"  refine tolean.TypeScript.Proof.evalReduce_foldl_val fs {fuel} ρ {str acc} {str param} _ {encY} {encX} {fn} {decY} ?_ items v hv\n" ++
          s!"  intro a x\n" ++ substHfs ++ unpack ++
          s!"  {casesOn decls vars}link_tac [{simpSet}]"
        continue
      let .list method := method | continue
      let (evalFn, want, result, fromLemma) := match method with
        | .map => ("evalMap", "", s!"List.map {encY} (List.map {fn} items)",
            s!"evalMap_map fs {fuel} ρ {str param} _ {encX} {encY} {fn}")
        | .mapIdx index => ("evalMapIdx", "", s!"List.map {encY} (List.mapIdx {fn} items)",
            s!"evalMapIdx_mapIdx fs {fuel} ρ {str param} {str index} _ {encX} {encY} {fn}")
        | .filter => ("evalFilter", "", s!"List.map {encX} (List.filter {fn} items)",
            s!"evalFilter_filter fs {fuel} ρ {str param} _ {encX} {fn}")
        -- `findLast` is `find` on the reversed list, which `link_tac` writes as
        -- `List.map encX` of the reversed elements, so the same lemma applies.
        | .any | .find | .findLast => ("evalFind", " true", s!"Option.map {encX} (List.find? {fn} items)",
            s!"evalFind_true fs {fuel} ρ {str param} _ {encX} {fn}")
        | .findIndex => ("evalFindIdx", "", s!"List.findIdx? {fn} items",
            s!"evalFindIdx_findIdx fs {fuel} ρ {str param} _ {encX} {fn}")
        | .all => ("evalFind", " false", s!"Option.map {encX} (List.find? (fun x => !({fn} x)) items)",
            s!"evalFind_false fs {fuel} ρ {str param} _ {encX} {fn}")
      let (indexArg, start, intros) := match method with
        -- The proof names the index `idx`, not by its name in the source,
        -- which could hide one of the lemma's hypotheses, such as `hI`.
        | .mapIdx index => (s!" {str index}", " 0", "idx x")
        | .findIndex => ("", " 0", "x")
        | _ => ("", "", "x")
      let vars := ("x", elem) :: scope.zipIdx.map fun ((_, t), i) => (s!"v{i}", t)
      loopLemmas := loopLemmas.push (r.cert lemmaName)
      thms := thms.push <|
        s!"theorem {lemmaName} {generic} (fs : List (tolean.DeclRef × List String × tolean.TypeScript.IR.Body)){hfs}\n" ++
        s!"    (fuel : Nat) (ρ : Env {nv}){hI} (items : {itemsTy}) :\n" ++
        s!"    tolean.TypeScript.IR.Expr.{evalFn} fs {fuel} ρ {str param}{indexArg} ({term cbBody}){want}{start}\n" ++
        s!"      (List.map {encX} items) = some ({result}) := by\n" ++
        s!"  refine tolean.TypeScript.Proof.{fromLemma} ?_ items\n" ++
        s!"  intro {intros}\n" ++ substHfs ++ unpack ++
        s!"  {casesOn decls vars}link_tac [{simpSet}]"
    let mut index := 0
    let mut returnsLoop := false
    for (stateNames, element, body, info) in loopsOf outBody do
      index := index + 1
      let lemmaName := s!"{name}_loop{index}"
      let some bodyStmt := loopBody syntaxBody info.span
        | throw s!"{file}: no loop at {info.span.start.line}:{info.span.start.col} in {name}"
      let some encX := encoderOf r info.elem | throw s!"{file}: cannot encode the elements of a loop in {name}"
      let state := stateNames.zip info.stateTypes
      let vars := state ++ info.scope
      let coded ← vars.mapM fun (n, t) => do
        let (some e, some dec) := (encoderOf r t, decoderOf r t)
          | throw s!"{file}: cannot encode the variable {n} in {name}"
        return (n, e, dec)
      let decode (ρ n : String) : String :=
        match coded.find? (·.1 == n) with
        | some (_, _, dec) => s!"({dec} ({ρ}.lookup {str n}))"
        | none => "default"
      let count := stateNames.length
      let upd (s ρ : String) : String :=
        (stateNames.zipIdx.foldl (init := ρ) fun acc (n, i) =>
          match coded.find? (·.1 == n) with
          | some (_, e, _) => s!"({acc}.set {str n} ({e} {project s count i}))"
          | none => acc)
      let decState (ρ : String) : String :=
        if count == 1 then decode ρ stateNames.head! else
          "(" ++ ", ".intercalate (stateNames.map (decode ρ)) ++ ")"
      let inv (ρ : String) : String :=
        " ∧ ".intercalate (coded.map fun (n, e, dec) =>
          s!"{ρ}.lookup {str n} = some ({e} ({dec} ({ρ}.lookup {str n})))")
      let scopeNames := info.scope.map (·.1)
      let stepLines := IR.indentBy "        " (body.lines names)
      -- Every binder has its type, as in the output's loop (see `IR.foldBinders`).
      let captured := if scopeNames.isEmpty then "" else
        s!"fun {" ".intercalate (info.scope.map fun (n, t) => s!"({n} : {t.print names})")} => "
      -- A loop that a `break` can end runs with `forIn`, and its step gives a
      -- `ForInStep` of the state. The type says `Id`, as `forIn` expects in the
      -- printed definition, so that the two `if`s have the same type and the
      -- link theorem can rewrite one with the other.
      -- In a loop that a `return` can end, the state starts with the value to
      -- return, which the lemma reads with `getRet`; `getS` reads the locals,
      -- and `init` starts the state with no value.
      let stateTy := match info.returns with
        | some ty =>
          let slotTy := (tolean.IR.Ty.option ty).print names
          if count == 0 then slotTy else s!"{slotTy} × {IR.foldState names info}"
        | none => IR.foldState names info
      let stepTy := if info.breaks then s!"Id (ForInStep ({stateTy}))" else stateTy
      let (getRet, getS, init) := if count == 0
        then (r.write "id" "id", "(fun _ => ())", s!"(fun _ => {r.write "none" "Option.none"})")
        else (r.write "Prod.fst" "Prod.fst", r.write "Prod.snd" "Prod.snd",
          s!"(fun s => ({r.write "none" "Option.none"}, s))")
      let encR := match info.returns with
        | some ty => (encoderOf r ty).getD "default"
        | none => "default"
      let stepFn (ρ : String) : String :=
        -- The result has its type too: alone, Lean would not coerce a `T` in
        -- the body to the state's `Option T`.
        s!"((({captured}fun {IR.foldBinders names stateNames element info} => (\n" ++ "\n".intercalate stepLines ++
          s!" : {stepTy}))" ++
          String.join (scopeNames.map fun n => s!" {decode ρ n}") ++ "))"
      let runLoop (ρ : String) : String :=
        if info.returns.isSome then s!"(Id.run (forIn items ({init} {decState ρ}) {stepFn ρ}))"
        else if info.breaks then s!"(Id.run (forIn items {decState ρ} {stepFn ρ}))"
        else s!"(List.foldl {stepFn ρ} {decState ρ} items)"
      -- What the evaluator's fold gives: the locals at the end of the loop,
      -- or the value to return.
      let result (ρ : String) : String :=
        if info.returns.isSome then
          s!"(tolean.TypeScript.Proof.retResult {encR} {getRet} {getS} (fun s ρ => {upd "s" "ρ"}) {ρ} {runLoop ρ})"
        else s!"(.normal {upd (runLoop ρ) ρ})"
      let loopLemma := if info.returns.isSome then "runFold_forInRet"
        else if info.breaks then "runFold_forIn" else "runFold_foldl"
      let loopArgs := if info.returns.isSome then s!"{encX} {encR} {getRet} {getS} {init}" else encX
      let initProof := if info.returns.isSome then " (fun _ => ⟨rfl, rfl⟩)" else ""
      let stepNames := if info.returns.isSome then
          ["tolean.TypeScript.Proof.retOutcome", "ForInStep.value"]
        else if info.breaks then ["tolean.TypeScript.Proof.stepOutcome", "ForInStep.value"] else []
      if info.returns.isSome then returnsLoop := true
      let depth := callDepth m bodyStmt
      let fuel := if depth == 0 then "fuel" else s!"(fuel + {depth})"
      -- A body with calls looks the functions up in the output, so the lemma
      -- is about the output's functions.
      let hfs := if depth == 0 then "" else s!" (hfs : fs = {outputFs})"
      let substHfs := if depth == 0 then "" else "    subst hfs\n"
      let hfsName := if depth == 0 then [] else [r.cert "decls"]
      -- `List (Option Int)`, with the parentheses that an element type needs.
      let itemsTy := (tolean.IR.Ty.list info.elem).print names
      let hypNames := (List.range coded.length).map (s!"h{·}")
      -- `obtain h0 := hI` would lose the name, so one hypothesis gets a `have`.
      let bindHyps := if hypNames.length == 1 then "have h0 := hI"
        else "obtain ⟨" ++ ", ".intercalate hypNames ++ "⟩ := hI"
      let generalize (ρ : String) (which : List (String × String × String)) : String :=
        String.join (which.zipIdx.map fun ((n, _, dec), i) =>
          s!"    generalize {dec} ({ρ}.lookup {str n}) = v{i} at h{i} ⊢\n")
      let stateCoded := coded.take count
      let destruct := if count ≤ 1 then "" else
        s!"    obtain ⟨{", ".intercalate ((List.range count).map (s!"s{·}"))}⟩ := s\n"
      let simpSet := ", ".intercalate (hfsName ++ stepNames ++ envLemmas ++ lemmaNames.toList ++
        loopLemmas.toList ++ defs)
      -- The values that one step sees: the element, the state, and the other
      -- locals, which the lemma generalizes to `v0`, `v1` and so on.
      let stateVars := if count ≤ 1 then ["s"].zip info.stateTypes
        else (List.range count).map (s!"s{·}") |>.zip info.stateTypes
      let loopVars := ("x", info.elem) :: stateVars ++ vars.zipIdx.map fun ((_, t), i) => (s!"v{i}", t)
      loopLemmas := loopLemmas.push (r.cert lemmaName)
      thms := thms.push <|
        s!"theorem {lemmaName} {generic} (fs : List (tolean.DeclRef × List String × tolean.TypeScript.IR.Body)){hfs}\n" ++
        s!"    (fuel : Nat) (items : {itemsTy}) (ρ : Env {nv}) (hI : {inv "ρ"}) :\n" ++
        s!"    tolean.TypeScript.IR.Body.runFold fs {fuel} {list (stateNames.map str)} {str element}\n" ++
        s!"      ({term body}) ρ (List.map {encX} items) =\n" ++
        s!"      some {result "ρ"} := by\n" ++
        s!"  refine tolean.TypeScript.Proof.{loopLemma} fs {fuel} _ {str element} _ {loopArgs} (fun s ρ => {upd "s" "ρ"})\n" ++
        s!"    (fun ρ => {decState "ρ"}) (fun ρ => {stepFn "ρ"}) (fun ρ => {inv "ρ"}){initProof} ?_ ?_ items ρ hI\n" ++
        s!"  · intro ρ s x hI\n" ++
        substHfs ++
        s!"    {bindHyps}\n    try simp only []\n" ++
        generalize "ρ" coded ++ destruct ++
        s!"    {casesOn decls loopVars}link_tac [{simpSet}, {", ".intercalate hypNames}]\n" ++
        s!"  · intro ρ hI\n" ++
        s!"    {bindHyps}\n    try simp only []\n" ++
        generalize "ρ" stateCoded ++
        -- With no locals in the state, the goal is `ρ = ρ`, which the step
        -- before may already close.
        s!"    all_goals simp [{", ".intercalate ((List.range count).map fun i => s!"Env.set_of_lookup _ _ _ h{i}")}]"
    -- The encoders follow the types of the output, which the translator has
    -- already worked out from the source's types.
    let some retEnc := encoderOf r outRet | throw s!"{file}: cannot encode the result of {name}"
    let args ← outParams.mapM fun (p, t) => do
      let some e := encoderOf r t | throw s!"{file}: cannot encode the parameter {p}"
      return s!"({e} {p})"
    let binders := " ".intercalate (params.map fun p => s!"({p.name} : _)")
    let call := " ".intercalate ((r.full s!"{transNs}.{name}" ++ callN) :: params.map (·.name))
    let retNames := if returnsLoop then ["tolean.TypeScript.Proof.retResult"] else []
    let simpSet := ", ".intercalate ([r.cert "decls"] ++ retNames ++ envLemmas ++ lemmaNames.toList ++
      loopLemmas.toList ++ defs)
    let some_ := r.write "some" "Option.some"
    let rfl := r.full "rfl"
    thms := thms.push <|
      s!"theorem {name}_link {generic} {binders} :\n" ++
      s!"    {r.full "tolean.TypeScript.IR.runIn"} (N := {nv}) {outputFs} ⟨\"\", {str name}⟩ {list args} =\n" ++
      s!"      {some_} ({retEnc} ({call})) := by\n" ++
      s!"  {casesOn decls outParams}link_tac [{simpSet}]" ++
      -- After a loop that a `return` can end, the evaluator matches on the
      -- loop's outcome, which is itself a match on the value to return. Once
      -- that match is split, the arms for a `break` or a `continue` close, and
      -- the arm for the end of the loop reads the locals from its state.
      -- `link_eqs` relates the loop's result to the printed loop's, whose
      -- `match`es have other auxiliary functions.
      (if returnsLoop then
        "\n  all_goals (try split at *)\n  all_goals (subst_vars; link_eqs; simp_all [List.lookup])" else "")
    thms := thms.push <|
      s!"theorem {name}_cert {generic} {binders} :\n" ++
      s!"    {r.eval "run"} (N := {nv}) {r.cert "program"} {str name} {list args} = {some_} ({retEnc} ({call})) :=\n" ++
      s!"  {r.full "tolean.TypeScript.Proof.decls_sound"} {rfl} {rfl} {rfl} {r.cert "program_translated"} {str name} _ 64 _\n" ++
      s!"    ({" ".intercalate (r.cert s!"{name}_link" :: params.map (·.name))})"
  return "\n".intercalate ([
    s!"-- Certificate written by tolean for {file}. Do not edit.",
    "import tolean.TypeScript.Spec.Lemmas.Eval",
    "import tolean.TypeScript.Syntax.Parser",
    "import tolean.TypeScript.Proof.Link",
    s!"import {leanModule}",
    "",
    s!"namespace {certNs}",
    "",
    "open tolean.TypeScript tolean.TypeScript.Eval tolean.TypeScript.Syntax",
    "",
    "-- The proofs pass the same lemmas everywhere, so some go unused.",
    "set_option linter.unusedSimpArgs false",
    "set_option linter.unusedVariables false",
    "",
    "/-- The program, as the parser read it. -/",
    s!"def program : tolean.TypeScript.Syntax.Module :=\n  {module m}",
    "",
    "/-- The source file, one line at a time. -/",
    s!"def sourceLines : List (List Char) := [\n  " ++
      ",\n  ".intercalate ((source.splitOn "\n").map fun line => s!"chars!{str line}") ++ "]",
    "",
    "def sourceChars : List Char := tolean.TypeScript.Syntax.joinLines sourceLines",
    "",
    "/-- The parser gives `program` for the source: the kernel runs the parser and",
    "compares the trees. So the theorems below are about the source file, and the",
    "printer that wrote `program` need not be trusted. -/",
    s!"theorem program_parsed : tolean.TypeScript.Syntax.parseChars sourceChars .{target.name.toLower} = Except.ok program :=",
    "  tolean.TypeScript.Syntax.parseChars_eq_of_parsesTo (by decide +kernel)",
    "",
    "/-- The Tolean IR, as the translator gives it for the program. -/",
    s!"def decls : List tolean.TypeScript.IR.Decl :=\n  {term decls}",
    "",
    "/-- The state that the translator starts from. The source text serves only in",
    "the message of a refusal, so the start leaves it out. -/",
    "def start : tolean.TypeScript.Translate.Ctx :=",
    s!"  \{ file := \"\", target := .{target.name.toLower}, src := #[], lineStarts := #[], fuel := 4 * sourceChars.length + 4 }",
    "",
    "/-- The translator gives `decls` for the program: the kernel runs it and",
    "compares the trees. With a `link` theorem for each function, the theorems",
    "below then trust neither the translator nor the printer. -/",
    "theorem program_translated : tolean.TypeScript.Proof.translatesTo program start decls = true := by",
    "  decide +kernel",
    ""] ++ encs.toList.map (· ++ "\n") ++ thms.toList.map (· ++ "\n") ++ [s!"end {certNs}", ""])

/-- The functions of `source` that get a certificate, and whether that is all
of them. -/
def certifiedFunctions (source : String) (target : Edition := .default) :
    Except String (List String × Bool) := do
  let m ← (parse source target).mapError (·.message)
  let all := m.decls.filterMap fun | .function _ _ n .. => some n | _ => none
  let fns := certifiable m
  return (fns, fns.length == all.length)

end tolean.TypeScript.Certify
