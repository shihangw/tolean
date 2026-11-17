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
  /-- The codec variables for the type parameters in the current declaration. -/
  codecs : List (String × String) := []

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

/-- The codec variable for a source type parameter. -/
def Refs.codec (r : Refs) (name : String) : Option String :=
  (r.codecs.find? (·.1 == name)).map (·.2)

/-- A local codec binder that cannot hide an identifier from the source. -/
def Refs.codecName (r : Refs) (name : String) : String :=
  let base := s!"toleanCodec_{name}"
  let candidates := (List.range (r.idents.length + 1)).map fun n =>
    base ++ String.join (List.replicate n "_")
  (candidates.find? fun candidate => !(r.idents.contains candidate)).getD (base ++ "_")

/-- The binders for codecs that a generic declaration needs. -/
def Refs.codecBinders (r : Refs) (nv : String) (params : List String) : String :=
  String.join (params.map fun name =>
    s!" \{{name} : Type} ({r.codecName name} : tolean.TypeScript.Eval.Codec {nv} {name})")

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
  -- A type parameter uses the codec that its function or interface certificate
  -- binds. A generic application is supported when every argument is such a
  -- parameter; other applications have no codec yet.
  | .param name => do return s!"({← r.codec name}.encode)"
  | .app ref args => do
    let codecs ← args.mapM fun
      | .param name => r.codec name
      | _ => none
    return s!"({r.cert s!"encode{ref.name}"} {String.intercalate " " codecs})"
  | .null | .tag _ | .map .. | .set _ | .except .. | .error | .date | .regexp | .ext .closure => none

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
  | .param name => do return s!"({← r.codec name}.decode)"
  | .app ref args => do
    let codecs ← args.mapM fun
      | .param name => r.codec name
      | _ => none
    return s!"({r.cert s!"decode{ref.name}"} {String.intercalate " " codecs})"
  | .null | .tag _ | .map .. | .set _ | .except .. | .error | .date | .regexp | .ext .closure => none

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
  | .forOfPattern s k p i b => .forOfPattern s k p i b :: stmtsOf b
  | .forStmt s i t u b => .forStmt s i t u b :: stmtsOf b
  | .whileStmt s t b => .whileStmt s t b :: stmtsOf b
  | .funDecl s n tps ps r b => .funDecl s n tps ps r b :: stmtsOf b
  | .switchStmt s d cs => .switchStmt s d cs :: cs.flatMap fun (_, body) => body.flatMap stmtsOf
  | s => [s]

partial def exprCalls : Expr → List String
  | .call _ (.ident _ f) args => f :: args.flatMap exprCalls
  | .call _ c args => exprCalls c ++ args.flatMap exprCalls
  | .paren _ e | .member _ e _ | .optMember _ e _ | .unary _ _ e | .prefix _ _ e | .postfix _ _ e
  | .asConst _ e | .satisfies _ e _ | .spread _ e =>
    exprCalls e
  | .index _ a b | .optIndex _ a b | .binary _ _ a b | .assign _ _ a b => exprCalls a ++ exprCalls b
  | .cond _ a b c => exprCalls a ++ exprCalls b ++ exprCalls c
  | .array _ es => es.flatMap exprCalls
  | .object _ ps => ps.flatMap fun
      | .keyValue _ _ v | .spread _ v => exprCalls v
      | .shorthand .. => []
  | .arrow _ _ _ body => exprCalls body
  | _ => []

/-- The text of each number literal in `e`. -/
partial def exprNumbers : Expr → List String
  | .number _ t => [t]
  | .call _ c args => exprNumbers c ++ args.flatMap exprNumbers
  | .paren _ e | .member _ e _ | .optMember _ e _ | .unary _ _ e | .prefix _ _ e | .postfix _ _ e
  | .asConst _ e | .satisfies _ e _ | .spread _ e =>
    exprNumbers e
  | .index _ a b | .optIndex _ a b | .binary _ _ a b | .assign _ _ a b => exprNumbers a ++ exprNumbers b
  | .cond _ a b c => exprNumbers a ++ exprNumbers b ++ exprNumbers c
  | .array _ es => es.flatMap exprNumbers
  | .object _ ps => ps.flatMap fun | .keyValue _ _ v => exprNumbers v | _ => []
  | .arrow _ _ _ body => exprNumbers body
  | _ => []

def stmtNumbers : Stmt → List String
  | .varDecl _ d => (d.init.map exprNumbers).getD []
  | .exprStmt _ e | .ifStmt _ e _ _ | .whileStmt _ e _ | .forOfStmt _ _ _ e _ | .forOfPattern _ _ _ e _ | .destructure _ _ _ _ e => exprNumbers e
  | .returnStmt _ e => (e.map exprNumbers).getD []
  | .forStmt _ i t u _ =>
    (((i.bind (·.init)).map exprNumbers).getD []) ++ ((t.map exprNumbers).getD []) ++ ((u.map exprNumbers).getD [])
  | _ => []

def stmtCalls : Stmt → List String
  | .varDecl _ d => (d.init.map exprCalls).getD []
  | .exprStmt _ e | .ifStmt _ e _ _ | .whileStmt _ e _ | .forOfStmt _ _ _ e _ | .forOfPattern _ _ _ e _ | .destructure _ _ _ _ e => exprCalls e
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
    | .arrow _ _ _ e | .spread _ e => subExprs e
    | .index _ a b | .optIndex _ a b | .binary _ _ a b | .assign _ _ a b => subExprs a ++ subExprs b
    | .cond _ a b c => subExprs a ++ subExprs b ++ subExprs c
    | .array _ es => es.flatMap subExprs
    | .object _ ps => ps.flatMap fun | .keyValue _ _ v => subExprs v | _ => []
    | _ => []

/-- The expressions that a statement holds, outside its nested statements. -/
def stmtExprs : Stmt → List Expr
  | .varDecl _ d => d.init.toList
  | .exprStmt _ e | .ifStmt _ e _ _ | .whileStmt _ e _ | .forOfStmt _ _ _ e _ | .forOfPattern _ _ _ e _ | .destructure _ _ _ _ e => [e]
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
abbrev Callback := CallbackKind × String × IR.Ty × IR.Expr × IR.CallbackInfo IR.TyExt × IR.Expr

/-- The type at a comparator's field path, in the translated declarations. -/
def keyPathType (decls : List IR.Decl) : IR.Ty → List String → Option IR.Ty
  | ty, [] => some ty
  | .struct ref, field :: rest => do
    let ty ← decls.findSome? fun
      | .struct name _ fields => if name == ref.name then fields.lookup field else none
      | _ => none
    keyPathType decls ty rest
  | _, _ => none

mutual
/-- List expressions whose encodings the sort link tactic can reconstruct. -/
def sortInputShape : IR.Expr → Bool
  | .var _ => true
  | .field e _ _ | .ascribe e _ => sortInputShape e
  | .ext .nullishFlatten [e] | .ext (.optField _ _) [e] => sortInputShape e
  | .coalesce a b _ => sortInputShape a && sortInputShape b
  | .ext .append es => sortInputShapes es
  | .list _ _ => true
  | .listMethod .map items _ _ _ _ | .listMethod .filter items _ _ _ _
  | .listMethod (.mapIdx _) items _ _ _ _ => sortInputShape items
  | .ext (.slice _ _) [items] | .ext .sliceInt (items :: _) => sortInputShape items
  | .call _ _ => true
  | .ite _ a b => sortInputShape a && sortInputShape b
  | _ => false

def sortInputShapes : List IR.Expr → Bool
  | [] => true
  | e :: es => sortInputShape e && sortInputShapes es
end

mutual

/-- `e` compares or subtracts numbers. A comparator of keys holds such a
test only for `number` keys. -/
partial def comparesNumbers : IR.Expr → Bool
  | .ext (.numberOp _) _ => true
  | .ext _ args => args.any comparesNumbers
  | .ite a b c => comparesNumbers a || comparesNumbers b || comparesNumbers c
  | .decide a | .not a | .neg a => comparesNumbers a
  | _ => false

/-- The callbacks in `e`, inner ones first, in the order of the source. -/
partial def exprCallbacks : IR.Expr → List Callback
  | .listMethod method items param elem body info =>
    exprCallbacks items ++ exprCallbacks body ++ [(.list method, param, elem, body, info, items)]
  | .listFold items init acc param elem body info =>
    exprCallbacks items ++ exprCallbacks init ++ exprCallbacks body ++ [(.fold acc, param, elem, body, info, items)]
  | .field a _ _ | .propNot a | .not a | .neg a | .isNone a | .isSome a | .decide a | .push _ a
  | .update _ _ a | .inject _ _ a | .ascribe a _ => exprCallbacks a
  | .ite a b c => exprCallbacks a ++ exprCallbacks b ++ exprCallbacks c
  | .matchNull _ a b _ | .coalesce a b _ | .intOp _ a b | .order _ a b | .division _ a b
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
  | .matchNull n a b _ => n :: exprNames a ++ exprNames b
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

/-- The names that a loop body reads. -/
partial def bodyNames : IR.Body → List String
  | .value e => exprNames e
  | .state _ | .yield .. | .done .. => []
  | .exit e _ | .throw e => exprNames e
  | .let _ e rest | .letTuple _ e rest => exprNames e ++ bodyNames rest
  | .letArray _ _ elems rest => elems.flatMap exprNames ++ bodyNames rest
  | .ite c a b => exprNames c ++ bodyNames a ++ bodyNames b
  | .matchNull _ _ a b | .matchTag _ _ _ _ _ a b => bodyNames a ++ bodyNames b
  | .letState _ branch rest => bodyNames branch ++ bodyNames rest
  | .fold _ _ body items rest _ => exprNames items ++ bodyNames body ++ bodyNames rest
  | .bind _ _ args rest | .letBorrow _ _ _ args rest => args.flatMap exprNames ++ bodyNames rest
  | .letCall _ _ _ value _ _ _ body args rest =>
    exprNames value ++ bodyNames body ++ args.flatMap exprNames ++ bodyNames rest
  | .letLifted _ e rest => exprNames e ++ bodyNames rest

/-- Whether a type contains a source type parameter. -/
partial def tyHasParam : IR.Ty → Bool
  | .param _ => true
  | .option t | .optional t | .list t | .set t => tyHasParam t
  | .tuple ts => ts.any tyHasParam
  | .app _ ts => ts.any tyHasParam
  | .map k v | .except k v => tyHasParam k || tyHasParam v
  | _ => false

/-- The callbacks in a body, inner ones first, in the order of the source. -/
partial def bodyCallbacks : IR.Body → List Callback
  | .value e => exprCallbacks e
  | .state _ | .yield .. | .done .. => []
  | .exit e _ => exprCallbacks e
  | .let _ e rest | .letTuple _ e rest => exprCallbacks e ++ bodyCallbacks rest
  | .letArray _ _ elems rest => elems.flatMap exprCallbacks ++ bodyCallbacks rest
  | .ite c a b => exprCallbacks c ++ bodyCallbacks a ++ bodyCallbacks b
  | .matchNull _ _ a b | .matchTag _ _ _ _ _ a b | .letState _ a b => bodyCallbacks a ++ bodyCallbacks b
  | .fold _ _ body items rest _ => exprCallbacks items ++ bodyCallbacks body ++ bodyCallbacks rest
  | .throw e => exprCallbacks e
  | .bind _ _ args rest | .letBorrow _ _ _ args rest => args.flatMap exprCallbacks ++ bodyCallbacks rest
  | .letCall _ _ _ _ _ _ _ body args rest =>
    args.flatMap exprCallbacks ++ bodyCallbacks body ++ bodyCallbacks rest
  | .letLifted _ _ rest => bodyCallbacks rest

end

mutual
/-- Free names of list inputs and their callbacks. Each callback removes
its own binders after visiting nested callbacks. -/
def sortInputNames : IR.Expr → List String
  | .listMethod method items param _ cb _ =>
    let bound := param :: (match method with | .mapIdx index => [index] | _ => [])
    sortInputNames items ++ (sortInputNames cb).filter (fun n => !bound.contains n)
  | .listFold items init acc param _ cb _ =>
    sortInputNames items ++ sortInputNames init ++
      (sortInputNames cb).filter (fun n => n != acc && n != param)
  | .field e _ _ | .proj e _ _ | .ascribe e _ | .decide e | .not e | .neg e
  | .isNone e | .isSome e | .propNot e | .inject _ _ e => sortInputNames e
  | .push n e | .update _ n e => n :: sortInputNames e
  | .matchNull n a b _ => n :: sortInputNames a ++ sortInputNames b
  | .intOp _ a b | .order _ a b | .division _ a b | .eq a b | .ne a b
  | .propAnd a b | .propOr a b | .and a b | .or a b | .coalesce a b _ =>
    sortInputNames a ++ sortInputNames b
  | .ext _ es | .call _ es | .list es _ | .tuple es => sortInputNamesList es
  | .ite c a b => sortInputNames c ++ sortInputNames a ++ sortInputNames b
  | .struct fields _ _ => sortInputFieldNames fields
  | .structUpdate base fields => sortInputNames base ++ sortInputFieldNames fields
  | .var n => [n]
  | .int _ | .none | .bool _ | .string _ | .enumCase .. | .tagValue _ => []

def sortInputNamesList : List IR.Expr → List String
  | [] => []
  | e :: es => sortInputNames e ++ sortInputNamesList es

def sortInputFieldNames : List (String × IR.Expr) → List String
  | [] => []
  | (_, e) :: fields => sortInputNames e ++ sortInputFieldNames fields
end

/-- Leading bindings remain in source order. A callback's scope determines
which of them precede it. -/
def leadingBindings : IR.Body → List (String × IR.Expr)
  | .let name value rest => (name, value) :: leadingBindings rest
  | _ => []

/-- A call's nullish branches, followed by its actual arguments.
The last flag records whether a statement narrowed the null arm. -/
abbrev ConditionalCall := List (String × Bool × IR.MatchNullKind × Bool) × List IR.Expr

def guardCondition (r : Refs) (guards : List (String × Bool × IR.MatchNullKind × Bool))
    (condition : String) : String :=
  guards.foldr (fun (n, valueBranch, kind, narrowedNull) rest =>
    match kind with
    | .nullable | .optional =>
      if valueBranch then s!"(match {n} with | .none => _root_.True | .some {n} => {rest})"
      else s!"(match {n} with | .none => {rest} | .some _ => _root_.True)"
    | .nullish =>
      let nullish := r.write "JSNullish" "tolean.TypeScript.JSNullish"
      if valueBranch then
        s!"(match {n} with | {nullish}.undefined => _root_.True | {nullish}.null => _root_.True | {nullish}.value {n} => {rest})"
      else
        s!"(match {n} with | {nullish}.undefined => {rest} | {nullish}.null => {rest} | {nullish}.value _ => _root_.True)"
    | .strictNull =>
      let nullish := r.write "JSNullish" "tolean.TypeScript.JSNullish"
      if valueBranch then
        s!"(match {n} with | {nullish}.undefined => (let {n} := {r.write "Option.join" "Option.join"} {n}; {rest}) | {nullish}.null => _root_.True | {nullish}.value {n} => (let {n} := _root_.Option.some {n}; {rest}))"
      else
        let rest := if narrowedNull then
          s!"(let {n} \{α : Type} : _root_.Option α := _root_.Option.none; {rest})" else rest
        s!"(match {n} with | {nullish}.undefined => _root_.True | {nullish}.null => {rest} | {nullish}.value _ => _root_.True)"
    | .strictUndefined =>
      let nullish := r.write "JSNullish" "tolean.TypeScript.JSNullish"
      if valueBranch then
        s!"(match {n} with | {nullish}.undefined => _root_.True | {nullish}.null => (let {n} := {r.write "Option.join" "Option.join"} {n}; {rest}) | {nullish}.value {n} => (let {n} := _root_.Option.some {n}; {rest}))"
      else
        s!"(match {n} with | {nullish}.undefined => {rest} | {nullish}.null => _root_.True | {nullish}.value _ => _root_.True)") condition

mutual
/-- Calls outside callback bodies. A source-call count below checks that no
call which needs a condition was hidden in a callback or another scope. -/
def conditionCalls (callee : String) : IR.Expr → List ConditionalCall
  | .call ref args => (if ref.name == callee then [([], args)] else []) ++ conditionCallsList callee args
  | .listMethod _ items _ _ _ _ => conditionCalls callee items
  | .listFold items init _ _ _ _ _ => conditionCalls callee items ++ conditionCalls callee init
  | .field e _ _ | .proj e _ _ | .ascribe e _ | .decide e | .not e | .neg e
  | .isNone e | .isSome e | .propNot e | .inject _ _ e | .push _ e | .update _ _ e =>
    conditionCalls callee e
  | .ite a b c => conditionCalls callee a ++ conditionCalls callee b ++ conditionCalls callee c
  | .matchNull n a b kind =>
    (conditionCalls callee a).map (fun (guards, args) => ((n, false, kind, false) :: guards, args)) ++
      (conditionCalls callee b).map (fun (guards, args) => ((n, true, kind, false) :: guards, args))
  | .intOp _ a b | .order _ a b | .division _ a b | .eq a b | .ne a b
  | .propAnd a b | .propOr a b | .and a b | .or a b | .coalesce a b _ =>
    conditionCalls callee a ++ conditionCalls callee b
  | .ext _ es | .list es _ | .tuple es => conditionCallsList callee es
  | .struct fields _ _ => conditionCallFields callee fields
  | .structUpdate base fields => conditionCalls callee base ++ conditionCallFields callee fields
  | .int _ | .none | .bool _ | .string _ | .var _ | .enumCase .. | .tagValue _ => []

def conditionCallsList (callee : String) : List IR.Expr → List ConditionalCall
  | [] => []
  | e :: es => conditionCalls callee e ++ conditionCallsList callee es

def conditionCallFields (callee : String) : List (String × IR.Expr) → List ConditionalCall
  | [] => []
  | (_, e) :: fields => conditionCalls callee e ++ conditionCallFields callee fields
end

def bodyConditionCalls (callee : String) : IR.Body → List ConditionalCall
  | .value e | .exit e _ => conditionCalls callee e
  | .let _ e rest | .letTuple _ e rest => conditionCalls callee e ++ bodyConditionCalls callee rest
  | .letState _ a b => bodyConditionCalls callee a ++ bodyConditionCalls callee b
  | .ite c a b => conditionCalls callee c ++ bodyConditionCalls callee a ++ bodyConditionCalls callee b
  | .matchNull n kind a b =>
    (bodyConditionCalls callee a).map (fun (guards, args) => ((n, false, kind, true) :: guards, args)) ++
      (bodyConditionCalls callee b).map (fun (guards, args) => ((n, true, kind, true) :: guards, args))
  -- Tagged branches rebind the scrutinee at a narrower type.
  -- Do not lift their conditions into the original parameter scope.
  | .matchTag .. => []
  | .state _ | .yield .. | .done .. => []
  | .letArray .. | .fold .. | .throw ..
  | .bind .. | .letCall .. | .letLifted .. | .letBorrow .. => []

/-- Tagged narrowing needs guarded conditions over the original union value. -/
def hasTaggedConditionScope : IR.Body → Bool
  | .matchTag .. => true
  | .let _ _ rest | .letTuple _ _ rest | .letArray _ _ _ rest
  | .bind _ _ _ rest | .letCall _ _ _ _ _ _ _ _ _ rest | .letLifted _ _ rest
  | .letBorrow _ _ _ _ rest =>
    hasTaggedConditionScope rest
  | .ite _ a b | .matchNull _ _ a b | .letState _ a b =>
    hasTaggedConditionScope a || hasTaggedConditionScope b
  | .fold _ _ body _ rest _ => hasTaggedConditionScope body || hasTaggedConditionScope rest
  | .value _ | .exit .. | .state _ | .yield .. | .done .. | .throw _ => false

/-- The body of the loop statement at `span`. -/
def loopBody (s : Stmt) (span : Span) : Option Stmt :=
  (stmtsOf s).findSome? fun
    | .forOfStmt sp _ _ _ body | .forOfPattern sp _ _ _ body => if sp == span then some body else none
    | .forStmt sp _ _ _ body => if sp == span then some body else none
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
partial def loopsOf : IR.Body → List (List String × String × IR.Body × IR.LoopInfo × IR.Expr)
  | .value _ | .state _ | .yield .. | .done .. | .exit .. => []
  | .let _ _ rest | .letArray _ _ _ rest | .letTuple _ _ rest => loopsOf rest
  | .ite _ a b | .matchNull _ _ a b | .matchTag _ _ _ _ _ a b => loopsOf a ++ loopsOf b
  | .letState _ branch rest => loopsOf branch ++ loopsOf rest
  | .fold names element body items rest info => loopsOf body ++ [(names, element, body, info, items)] ++ loopsOf rest
  | .throw _ => []
  | .letCall _ _ _ _ _ _ _ body _ rest => loopsOf body ++ loopsOf rest
  | .bind _ _ _ rest | .letLifted _ _ rest | .letBorrow _ _ _ _ rest => loopsOf rest

/-- The closure values that calls in a body require from their environment. -/
def closureReads : IR.Body → List (String × IR.Expr)
  | .value _ | .state _ | .yield .. | .done .. | .exit .. | .throw _ => []
  | .let _ _ rest | .letArray _ _ _ rest | .letTuple _ _ rest |
    .bind _ _ _ rest | .letLifted _ _ rest | .letBorrow _ _ _ _ rest => closureReads rest
  | .ite _ a b | .matchNull _ _ a b | .matchTag _ _ _ _ _ a b |
    .letState _ a b => closureReads a ++ closureReads b
  | .fold _ _ body _ rest _ => closureReads body ++ closureReads rest
  | .letCall _ _ name value _ _ _ body _ rest =>
    (name, value) :: closureReads body ++ closureReads rest

/-- `s`, the state of a loop with the locals `names`, as the path to one of
them: `s`, `s.1`, `s.2.1`, and so on. -/
def project (s : String) (count index : Nat) : String :=
  if count == 1 then s
  else
    let seconds := String.join (List.replicate index ".2")
    if index + 1 == count then s!"{s}{seconds}" else s!"{s}{seconds}.1"

/-- A closure needs its syntax tree as a term, not the debug printer's
`<statement>` marker. Other operations use their derived representation. -/
private def exprExtTerm (x : IR.ExprExt) (prec : Nat) : Std.Format :=
  match x with
  | .closure params body =>
    Std.Format.text s!"(tolean.TypeScript.IR.ExprExt.closure {list (params.map str)} {stmt body})"
  | _ => reprPrec x prec

local instance : Repr IR.ExprExt := ⟨exprExtTerm⟩

/-- A value as a Lean term. The kernel checks that it is the translator's
output, so this printer need not be trusted. -/
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
  let parsed ← (Syntax.parse source target).mapError (·.render file)
  let hasClasses := parsed.decls.any (· matches .classDecl _)
  if !(Eval.borrowsOf ⟨[("", m)], ""⟩).isEmpty then
    throw s!"{file}: a map borrow has no certificate yet"
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
  -- `JSON.stringify` is opaque in the output and in the interpreter, so no
  -- proof links one to the other.
  if m.decls.any fun d => match d with
      | .function _ _ _ _ _ _ body =>
        ((stmtsOf body).flatMap stmtExprs).any fun e => (subExprs e).any fun
          | .call _ (.member _ (.ident _ "JSON") _) _ => true
          | _ => false
      | _ => false then
    throw s!"{file}: JSON.stringify has no certificate"
  let nv := names.typeParam
  -- Every theorem is about every number model. A sort reads the signs of
  -- `-1` and `1`, which hold in every model with the laws of safe integers,
  -- so the theorems of a file that sorts take those laws as hypotheses.
  let sorts := decls.any fun
    | .function _ _ _ body => (bodyCallbacks body).any (·.1 matches .list (.sortWith _))
    | _ => false
  let laws := if sorts then s!" [tolean.TypeScript.SafeIntLaws {nv}]" else ""
  let numericSorts := decls.any fun
    | .function _ _ _ body => (bodyCallbacks body).any fun (method, _, _, cb, _, _) =>
        (method matches .list (.sortWith _)) && comparesNumbers cb
    | _ => false
  let laws := laws ++ if numericSorts then s!" [tolean.TypeScript.NumberOrderLaws {nv}]" else ""
  let differences := numericSorts && (functionsOf m).any fun (_, _, _, body) =>
    ((stmtsOf body).flatMap stmtExprs).any fun e => (subExprs e).any fun
      | .call _ (.member _ _ method) [.arrow _ _ [a, b] cb] =>
        (method == "sort" || method == "toSorted") &&
          ((Translate.keyComparator? a.name b.name cb).getD []).any (·.2.1)
      | _ => false
  let laws := laws ++ if differences then s!" [tolean.TypeScript.SpecialValueLaws {nv}]" else ""
  let generic := s!"\{{nv} : Type} [tolean.TypeScript.JSNumber {nv}]{laws}"
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
      let structCodecs := typeParams.map fun p => (p, r.codecName p)
      let structRefs := { r with codecs := structCodecs }
      let structGeneric := generic ++ structRefs.codecBinders nv typeParams
      let structType := if typeParams.isEmpty then structTy name else
        (IR.Ty.app ⟨"", name⟩ (typeParams.map IR.Ty.param) : IR.Ty).print names
      let codecArgs := String.join (typeParams.map fun p => s!" ({structRefs.codecName p})")
      let decodeCall := if typeParams.isEmpty then s!"decode{name}"
        else s!"(decode{name}{codecArgs})"
      let decodeEncodeLaw := if typeParams.isEmpty then s!"decode{name}_encode{name}"
        else s!"(decode{name}_encode{name}{codecArgs})"
      let encodeNeNullLaw := if typeParams.isEmpty then s!"encode{name}_ne_null"
        else s!"(encode{name}_ne_null{codecArgs})"
      -- The encoder of an interface that refers to itself would be recursive.
      if allFields.any (fun (_, t) => t.refs.any (·.name == name)) then
        throw s!"{file}: the recursive interface {name} has no certificate yet"
      -- An optional field is a key only when it holds a value, as in an
      -- object literal that leaves it out.
      let parts ← allFields.mapM fun (f, t) => do
        if let .tag v := t then return (s!"({str f}, Val.str {r.jsString v})", false)
        if let .optional u := t then
          let some e := encoderOf structRefs u | throw s!"{file}: cannot encode the field {name}.{f}"
          return (s!"({r.eval "encField"} {str f} {e} x.{f})", true)
        let some e := encoderOf structRefs t | throw s!"{file}: cannot encode the field {name}.{f}"
        return (s!"({str f}, {e} x.{f})", false)
      let hasOptional := parts.any (·.2)
      let objList := if hasOptional then
          " ++ ".intercalate (parts.map fun (p, opt) => if opt then p else s!"[{p}]")
        else list (parts.map (·.1))
      -- The structure has no tag fields, so the decoder reads none.
      let fields := allFields.filter fun (_, t) => !(t matches .tag _)
      let decs ← fields.mapM fun (f, t) => do
        let some dec := decoderOf structRefs t | throw s!"{file}: cannot decode the field {name}.{f}"
        return (f, dec)
      let some_ := ", ".intercalate (decs.map fun (f, dec) => s!"{f} := {dec} (fs.lookup {str f})")
      let none_ := ", ".intercalate (decs.map fun (f, dec) => s!"{f} := {dec} (none : Option (Val {nv}))")
      encs := encs.push s!"def encode{name} {structGeneric} (x : {structType}) : Val {nv} := Val.obj {if hasOptional then s!"({objList})" else objList}"
      encs := encs.push <|
        s!"def decode{name} {structGeneric} : Option (Val {nv}) → {structType}\n" ++
        s!"  | some (.obj fs) => \{ {some_} }\n" ++
        s!"  | _ => \{ {none_} }"
      -- With optional fields, the proof splits each into its two cases.
      let optionalFields := fields.filterMap fun (f, t) => if t matches .optional _ then some f else none
      let splitOptional := if optionalFields.isEmpty then "cases x"
        else s!"obtain ⟨{", ".intercalate (fields.map fun (f, _) => s!"x_{f}")}⟩ := x\n  " ++
          String.join (optionalFields.map fun f => s!"cases x_{f} <;> ")
      encs := encs.push <|
        s!"@[simp] theorem decode{name}_encode{name} {structGeneric} (x : {structType}) : decode{name}{codecArgs} (some (encode{name} ({nv} := {nv}){codecArgs} x)) = x := by\n" ++
        s!"  {splitOptional}{if optionalFields.isEmpty then "; " else ""}simp [decode{name}, encode{name}, List.lookup, encList{if typeParams.isEmpty then "" else ", " ++ String.intercalate ", " (typeParams.map fun p => s!"{structRefs.codecName p}.decode_encode, {structRefs.codecName p}.encode_ne_null, {structRefs.codecName p}.encode_ne_undefined")}]"
      encs := encs.push <|
        s!"@[simp] theorem encode{name}_ne_null {structGeneric} (x : {structType}) : encode{name} ({nv} := {nv}){codecArgs} x ≠ Val.null := by\n" ++
        s!"  simp [encode{name}]"
      encs := encs.push <|
        s!"@[simp] theorem encode{name}_ne_undefined {structGeneric} (x : {structType}) : encode{name} ({nv} := {nv}){codecArgs} x ≠ Val.undefined := by\n" ++
        s!"  simp [encode{name}]"
      -- An array of the interface, as a loop over it reads its variable back.
      -- `simp` cannot find this from `decList_list` when the fields nest, so
      -- the certificate states it.
      encs := encs.push <|
        s!"@[simp] theorem decList_decode{name} {structGeneric} (xs : List {structType}) : decList {decodeCall} (some (Val.list (List.map (encode{name} ({nv} := {nv}){codecArgs}) xs))) = xs :=\n" ++
        s!"  decList_list _ _ {decodeEncodeLaw} xs"
      -- The same for an array of nullable values, which `simp` would
      -- otherwise reach only through side conditions that it cannot discharge
      -- once it unfolds the encoder.
      encs := encs.push <|
        s!"@[simp] theorem decList_decNull_decode{name} {structGeneric} (xs : List (Option {structType})) : decList (decNull {decodeCall}) (some (Val.list (List.map (encNull (encode{name} ({nv} := {nv}){codecArgs})) xs))) = xs :=\n" ++
        s!"  decList_list_null _ _ {decodeEncodeLaw} {encodeNeNullLaw} xs"
      unless typeParams.isEmpty do
        let genericTy := (IR.Ty.app ⟨"", name⟩ (typeParams.map IR.Ty.param) : IR.Ty).print names
        encs := encs.push <|
          s!"def codec{name} {structGeneric} : tolean.TypeScript.Eval.Codec {nv} ({genericTy}) where\n" ++
          s!"  encode x := .list [encode{name}{codecArgs} x]\n" ++
          s!"  decode\n    | some (.list [v]) => decode{name}{codecArgs} (some v)\n" ++
          s!"    | _ => decode{name}{codecArgs} none\n" ++
          s!"  decode_encode x := by simp [decode{name}_encode{name}]\n" ++
          s!"  encode_ne_null x := by simp\n" ++
          s!"  encode_ne_undefined x := by simp"
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
  let defs := [r.write "JSNumber.countUp?_eq_of_isSome" "tolean.TypeScript.JSNumber.countUp?_eq_of_isSome"] ++
    (decls.flatMap fun
      | .function name _ _ body =>
        r.full s!"{transNs}.{name}" ::
          body.lifted.map (fun (ref, _, _, _) => r.full s!"{transNs}.{ref.name}")
      | _ => [])
  let outputFs := s!"({r.full "tolean.TypeScript.IR.functionsOf"} [(\"\", {r.cert "decls"})])"
  let envLemmas := ["Env.set_cons", "Env.lookup_cons", "Env.lookup_set_same", "Env.lookup_set_ne",
    "Env.set_set", "Env.length_set"].map r.eval
  let mut loopLemmas : Array String := #[]
  let mut conditionalLemmas : List String := []
  let mut thms : Array String := #[]
  -- The translator requires a callee before its caller, so the condition
  -- of a callee is available when the caller's theorem is written.
  let mut functionConditions : List (String × (List (String × IR.Ty) × List String)) := []
  for d in m.decls do
    let .function _ _ name typeParams params _ syntaxBody := d | continue
    unless fns.contains name do continue
    let some (.function _ outParams outRet outBody) := decls.find? fun
        | .function n .. => n == name
        | _ => false
      | throw s!"{file}: no translation of {name}"
    let functionCodecs := typeParams.map fun p => (p, r.codecName p)
    let r := { r with codecs := functionCodecs }
    let functionGeneric := generic ++ r.codecBinders nv typeParams
    let codecLemmas := typeParams.flatMap fun p =>
      let c := r.codecName p
      [s!"{c}.decode_encode", s!"{c}.encode_ne_null", s!"{c}.encode_ne_undefined"]
    -- A callback gets a lemma before the loops, because a loop's body can
    -- hold one, and before the callbacks that hold it.
    let mut cbIndex := 0
    let mut obligations : List (String × String) := []
    let mut inputConditions : List String := []
    let mut literalMaps : List String := []
    let callbacks := bodyCallbacks outBody
    let parentOf := fun span => callbacks.find? fun (_, _, _, cb, _, _) =>
      (exprCallbacks cb).any fun (_, _, _, _, child, _) => child.span == span
    let mut callbackConditions : List (Span × String) := []
    let mut loopConditions : List (Span × String) := []
    let mut callbackCalls : List String := []
    let enclosingLoopsOf := fun span => (loopsOf outBody).filter fun (_, _, body, _, _) =>
      (bodyCallbacks body).any fun (_, _, _, _, child, _) => child.span == span
    let parentLoopOf := fun span => (loopsOf outBody).find? fun (_, _, body, _, _) =>
      (loopsOf body).any fun (_, _, _, child, _) => child.span == span
    for (method, param, elem, cbBody, info, items) in bodyCallbacks outBody do
      cbIndex := cbIndex + 1
      let lemmaName := s!"{name}_cb{cbIndex}"
      let parent := parentOf info.span
      let enclosingLoop := (enclosingLoopsOf info.span).head?
      let mut childConditions := callbackConditions.filterMap fun (span, condition) =>
        match parentOf span with
        | some (_, _, _, _, parentInfo, _) => if parentInfo.span == info.span then some condition else none
        | none => none
      for (callee, (formals, conditions)) in functionConditions do
        if conditions.isEmpty then continue
        for (guards, actuals) in conditionCalls callee cbBody do
          unless actuals.length == formals.length do
            throw s!"{file}: missing callback argument for a sort condition in {name}"
          let available := param :: info.scope.map (·.1)
          unless guards.all (fun (n, _, _) => available.contains n) &&
              (actuals.zip formals).all (fun (e, _, ty) =>
              (sortInputNames e).all available.contains &&
              (!(ty matches .list _) || sortInputShape e)) do
            throw s!"{file}: callback sort arguments must be reachable from its element or captured inputs in {name}"
          for (stateNames, _, _, _, _) in enclosingLoopsOf info.span do
            if actuals.any (fun e => (sortInputNames e).any stateNames.contains) ||
                guards.any (fun (n, _, _) => stateNames.contains n) then
              throw s!"{file}: a sort condition depends on changing loop state in {name}"
          callbackCalls := callee :: callbackCalls
          for (_, ty) in formals do
            let .list itemTy := ty | continue
            let some enc := encoderOf r itemTy | continue
            literalMaps := literalMaps ++ [s!"← List.map_singleton (f := {enc})",
              s!"← List.map_cons (f := {enc})"]
          for condition in conditions do
            let binders := " ".intercalate (formals.map fun (p, t) => s!"({p} : {t.print names})")
            let arguments := " ".intercalate (actuals.map fun e => s!"({e.print names})")
            childConditions := childConditions ++ [guardCondition r guards s!"((fun {binders} => {condition}) {arguments})"]
      unless childConditions.isEmpty || (method matches .list .map | .list .filter) do
        throw s!"{file}: sort conditions in this callback need an element-restricted link lemma in {name}"
      if comparesNumbers cbBody || !childConditions.isEmpty then
        let outerScope := match parent, enclosingLoop with
          | some (_, p, ty, _, parentInfo, _), _ => (p, ty) :: parentInfo.scope
          | none, some (_, p, _, loopInfo, _) => (p, loopInfo.elem) :: loopInfo.scope
          | none, none => outParams
        if info.scope.any (fun (n, ty) => (outerScope.lookup n).any (fun outer => outer.print names != ty.print names)) then
          throw s!"{file}: sort conditions across an enclosing nullable narrowing need scope propagation in {name}"
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
        | .list (.sortWith other) =>
          s!"fun ({param} : {elem.print names}) ({other} : {elem.print names}) => "
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
      let simpSet := ", ".intercalate (hfsName ++ envLemmas ++ lemmaNames.toList ++ codecLemmas ++ loopLemmas.toList ++ defs ++ hypNames)
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
          s!"theorem {lemmaName} {functionGeneric} (fs : List (tolean.DeclRef × List String × tolean.TypeScript.IR.Body)){hfs}\n" ++
          s!"    (fuel : Nat) (ρ : Env {nv}){hI} (items : {itemsTy}) (v : Val {nv})\n" ++
          s!"    (hv : {encY} ({decY} (some v)) = v) :\n" ++
          s!"    tolean.TypeScript.IR.Expr.evalReduce fs {fuel} ρ {str acc} {str param} ({term cbBody})\n" ++
          s!"      v (List.map {encX} items) = some ({encY} (List.foldl {fn} ({decY} (some v)) items)) := by\n" ++
          s!"  refine tolean.TypeScript.Proof.evalReduce_foldl_val fs {fuel} ρ {str acc} {str param} _ {encY} {encX} {fn} {decY} ?_ items v hv\n" ++
          s!"  intro a x\n" ++ substHfs ++ unpack ++
          s!"  {casesOn decls vars}link_tac [{simpSet}]"
        continue
      let .list method := method | continue
      -- A sort: the lemma needs the comparator to be consistent for every
      -- list. Its keys come from the source, and `sort_tac` shows that the
      -- comparator's sign is their lexicographic comparison, which
      -- `Std.TransCmp` says is a total preorder. A number key instead uses
      -- consistency on the input and an explicit hypothesis on its keys.
      if let .sortWith other := method then
        let some (.call _ _ [.arrow _ _ [p, q] arrowBody]) := callAt syntaxBody info.span
          | throw s!"{file}: no comparator at {info.span.start.line}:{info.span.start.col} in {name}"
        let some keys := Translate.keyComparator? p.name q.name arrowBody
          | throw s!"{file}: the comparator in {name} does not compare keys"
        let elemTy := elem.print names
        if comparesNumbers cbBody then
          conditionalLemmas := conditionalLemmas ++ [r.cert lemmaName]
          literalMaps := literalMaps ++ [s!"← List.map_singleton (f := {encX})",
            s!"← List.map_cons (f := {encX})"]
          let nested := parent.isSome || enclosingLoop.isSome
          let bindings := if nested then [] else (leadingBindings outBody).filter fun (n, _) =>
            info.scope.any fun (p, _) => p == n
          let mut available := if nested then info.scope.map (·.1) else outParams.map (·.1)
          for (stateNames, _, _, _, _) in enclosingLoopsOf info.span do
            if (sortInputNames items).any stateNames.contains then
              throw s!"{file}: a sort condition depends on changing loop state in {name}"
          if let some (_, loopElement, _, loopInfo, _) := enclosingLoop then
            let callbackParams := callbacks.filterMap fun (_, p, _, cb, _, _) =>
              if (exprCallbacks cb).any (fun (_, _, _, _, child, _) => child.span == info.span) then some p else none
            let reachable := loopElement :: loopInfo.scope.map (·.1) ++ callbackParams
            unless (sortInputNames items).all reachable.contains do
              throw s!"{file}: a loop sort condition depends on body locals in {name}"
          for (localName, value) in bindings do
            unless sortInputShape value && !(sortInputNames value).isEmpty &&
                (sortInputNames value).all available.contains do
              throw s!"{file}: the sorted list must be reachable from parameters through list bindings in {name}"
            available := localName :: available
          unless !(sortInputNames items).isEmpty && (sortInputNames items).all available.contains &&
              scope.isEmpty && sortInputShape items do
            throw s!"{file}: the sorted list must be reachable from parameters and its comparator must not capture locals in {name}"
          let lets := String.join (bindings.map fun (n, e) => s!"let {n} := {e.print names}; ")
          let input := s!"({lets}{items.print names})"
          if keys.length > 1 then
            let subtype := "{ x : " ++ elemTy ++ " // x ∈ items }"
            let mut hypotheses := ""
            let mut instances := ""
            let mut facts := ""
            let mut comparisons : List String := []
            for ((path, difference, up), ki) in keys.zipIdx do
              let some ty := keyPathType decls elem path
                | throw s!"{file}: cannot read a comparator key type in {name}"
              let key := s!"(fun ({param} : {elemTy}) => {".".intercalate (param :: path)})"
              let numeric := ty matches .number
              if numeric then
                let hn := s!"hkeys{ki}"
                let hname := s!"{name}_sort_precondition{obligations.length}"
                if r.idents.contains hname then
                  throw s!"{file}: reserved certificate hypothesis name {hname}"
                let predicate := if difference then "isFinite" else "isNaN"
                let truth := if difference then "true" else "false"
                let condition := fun xs => s!"∀ _sortItem' ∈ {xs}, tolean.TypeScript.JSNumber.{predicate} ({key} _sortItem') = {truth}"
                hypotheses := hypotheses ++ s!" ({hn} : {condition "items"})"
                if parent.isSome then
                  callbackConditions := callbackConditions ++ [(info.span, condition input)]
                else if let some (_, _, _, loopInfo, _) := enclosingLoop then
                  loopConditions := loopConditions ++ [(loopInfo.span, condition input)]
                else
                  obligations := obligations ++ [(hname, condition input)]
                  inputConditions := inputConditions ++ [condition input]
                let validity := if difference then
                  s!"tolean.TypeScript.SpecialValueLaws.isFinite_not_nan ({hn} a.val a.property)"
                  else s!"{hn} a.val a.property"
                instances := instances ++
                  s!"    letI : Std.TransCmp (fun (a b : {subtype}) => tolean.TypeScript.Proof.numberOrder ({key} a.val) ({key} b.val)) :=\n" ++
                  s!"      tolean.TypeScript.Proof.transCmp_numberOrder (fun (a : {subtype}) => {key} a.val) (fun a => {validity})\n"
                facts := facts ++ s!"    have h{ki}a := {hn} a.val a.property\n    have h{ki}b := {hn} b.val b.property\n"
              let cmp := if numeric then
                s!"(fun (a b : {subtype}) => tolean.TypeScript.Proof.numberOrder ({key} a.val) ({key} b.val))"
                else s!"({r.full "compareOn"} (fun (a : {subtype}) => {key} a.val))"
              comparisons := comparisons ++ [if up then cmp else s!"(fun (a b : {subtype}) => {cmp} b a)"]
            let o := match comparisons.reverse with
              | [] => "(fun _ _ => Ordering.eq)"
              | last :: rest => rest.foldl (fun acc c => s!"({r.full "compareLex"} {c} {acc})") last
            loopLemmas := loopLemmas.push (r.cert lemmaName)
            thms := thms.push <|
              s!"theorem {lemmaName} {functionGeneric} (fs : List (tolean.DeclRef × List String × tolean.TypeScript.IR.Body)){hfs}\n" ++
              s!"    (fuel : Nat) (ρ : Env {nv}) (items : {itemsTy}){hypotheses} :\n" ++
              s!"    tolean.TypeScript.Eval.sortValues (tolean.TypeScript.IR.Expr.evalCompare fs {fuel} ρ {str param} {str other} ({term cbBody}))\n" ++
              s!"      (List.map {encX} items) = some (List.map {encX} (tolean.TypeScript.JSNumber.sortWith {fn} items)) := by\n" ++
              s!"  refine tolean.TypeScript.Proof.sortValues_sortWith_on fs {fuel} ρ {str param} {str other} _ {encX} {fn} ?_ (fun _ => by simp) items ?_\n" ++
              s!"  · intro x y\n    {casesOn decls [("x", elem), ("y", elem)]}link_tac [{simpSet}]\n" ++
              "  ·\n" ++ instances ++
              s!"    apply tolean.TypeScript.Proof.consistentOn_of_transCmp_on items {o}\n" ++
              "    intro a b\n" ++ facts ++
              "    simp only []\n    repeat' split\n" ++
              "    all_goals simp_all [tolean.TypeScript.Proof.numberOrder, tolean.TypeScript.Proof.compareSign_sub,\n" ++
              "      tolean.TypeScript.compareSign_one, tolean.TypeScript.compareSign_zero,\n" ++
              "      tolean.TypeScript.compareSign_neg_one, tolean.TypeScript.compareSign_neg_zero,\n" ++
              "      compareLex, compareOn, Ordering.then, tolean.TypeScript.JSString.compare_of_lt,\n" ++
              "      tolean.TypeScript.JSString.compare_of_gt, tolean.TypeScript.JSString.compare_of_eq,\n" ++
              "      tolean.TypeScript.Proof.int_compare_of_lt, tolean.TypeScript.Proof.int_compare_of_gt,\n" ++
              "      tolean.TypeScript.Proof.int_compare_of_eq]"
            continue
          let [(path, difference, up)] := keys
            | throw s!"{file}: empty comparator keys in {name}"
          let key := s!"(fun ({param} : {elemTy}) => {".".intercalate (param :: path)})"
          let hname := s!"{name}_sort_precondition" ++
            if obligations.isEmpty then "" else toString obligations.length
          if r.idents.contains hname then
            throw s!"{file}: reserved certificate hypothesis name {hname}"
          let predicate := if difference then "isFinite" else "isNaN"
          let truth := if difference then "true" else "false"
          let condition := fun items => s!"∀ _sortItem' ∈ {items}, tolean.TypeScript.JSNumber.{predicate} ({key} _sortItem') = {truth}"
          let orderLemma := "tolean.TypeScript.Proof.consistentOn_numberOrder" ++ if up then "" else "_reverse"
          let (left, right) := if up then ("a", "b") else ("b", "a")
          let consistency := if difference then
            s!"  · rw [tolean.TypeScript.Proof.consistentOn_congr_on (fun a ha b hb =>\n" ++
            s!"      tolean.TypeScript.Proof.compareSign_sub (hkeys {left} h{left}) (hkeys {right} h{right}))]\n" ++
            s!"    exact {orderLemma} {key} items (fun x hx => tolean.TypeScript.SpecialValueLaws.isFinite_not_nan (hkeys x hx))"
            else
            s!"  · have hs : ∀ a b, tolean.TypeScript.JSNumber.compareSign ({fn} a b) =\n" ++
            s!"        some (tolean.TypeScript.Proof.numberOrder ({key} {left}) ({key} {right})) := by\n" ++
            "      intro a b\n      simp only []\n      unfold tolean.TypeScript.Proof.numberOrder\n      repeat' split\n" ++
            "      all_goals simp_all [tolean.TypeScript.compareSign_one, tolean.TypeScript.compareSign_zero,\n" ++
            "        tolean.TypeScript.compareSign_neg_one, tolean.TypeScript.compareSign_neg_zero]\n" ++
            s!"    simpa only [hs] using {orderLemma} {key} items hkeys"
          if parent.isSome then
            callbackConditions := callbackConditions ++ [(info.span, condition input)]
          else if let some (_, _, _, loopInfo, _) := enclosingLoop then
            loopConditions := loopConditions ++ [(loopInfo.span, condition input)]
          else
            obligations := obligations ++ [(hname, condition input)]
            inputConditions := inputConditions ++ [condition input]
          loopLemmas := loopLemmas.push (r.cert lemmaName)
          thms := thms.push <|
            s!"theorem {lemmaName} {functionGeneric} (fs : List (tolean.DeclRef × List String × tolean.TypeScript.IR.Body)){hfs}\n" ++
            s!"    (fuel : Nat) (ρ : Env {nv}) (items : {itemsTy}) (hkeys : {condition "items"}) :\n" ++
            s!"    tolean.TypeScript.Eval.sortValues (tolean.TypeScript.IR.Expr.evalCompare fs {fuel} ρ {str param} {str other} ({term cbBody}))\n" ++
            s!"      (List.map {encX} items) = some (List.map {encX} (tolean.TypeScript.JSNumber.sortWith {fn} items)) := by\n" ++
            s!"  refine tolean.TypeScript.Proof.sortValues_sortWith_on fs {fuel} ρ {str param} {str other} _ {encX} {fn} ?_\n" ++
            s!"    (fun _ => by simp) items ?_\n" ++
            s!"  · intro x y\n    {casesOn decls [("x", elem), ("y", elem)]}link_tac [{simpSet}]\n" ++
            consistency
          continue
        let keyCmp : List String × Bool × Bool → String := fun (path, _, up) =>
          let key := s!"(fun ({param} : {elemTy}) => {".".intercalate (param :: path)})"
          let cmp := s!"({r.full "compareOn"} {key})"
          if up then cmp else s!"(fun (x y : {elemTy}) => {cmp} y x)"
        let o := match (keys.map keyCmp).reverse with
          | [] => "(fun _ _ => Ordering.eq)"
          | last :: rest => rest.foldl (fun acc c => s!"({r.full "compareLex"} {c} {acc})") last
        let vars := ("x", elem) :: ("y", elem) :: scope.zipIdx.map fun ((_, t), i) => (s!"v{i}", t)
        loopLemmas := loopLemmas.push (r.cert lemmaName)
        thms := thms.push <|
          s!"theorem {lemmaName} {functionGeneric} (fs : List (tolean.DeclRef × List String × tolean.TypeScript.IR.Body)){hfs}\n" ++
          s!"    (fuel : Nat) (ρ : Env {nv}){hI} (items : {itemsTy}) :\n" ++
          s!"    tolean.TypeScript.Eval.sortValues (tolean.TypeScript.IR.Expr.evalCompare fs {fuel} ρ {str param} {str other} ({term cbBody}))\n" ++
          s!"      (List.map {encX} items) = some (List.map {encX} (tolean.TypeScript.JSNumber.sortWith {fn} items)) := by\n" ++
          s!"  refine tolean.TypeScript.Proof.sortValues_sortWith fs {fuel} ρ {str param} {str other} _ {encX} {fn} ?_\n" ++
          s!"    (fun _ => by simp) (tolean.TypeScript.Proof.consistentOn_of_transCmp {o} (by sort_tac)) items\n" ++
          s!"  intro x y\n" ++ substHfs ++ unpack ++
          s!"  {casesOn decls vars}link_tac [{simpSet}]"
        continue
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
        -- Written above.
        | .sortWith _ => ("", "", "", "")
      let (indexArg, start, intros) := match method with
        -- The proof names the index `idx`, not by its name in the source,
        -- which could hide one of the lemma's hypotheses, such as `hI`.
        | .mapIdx index => (s!" {str index}", " 0", "idx x")
        | .findIndex => ("", " 0", "x")
        | _ => ("", "", "x")
      if !childConditions.isEmpty then
        unless method == .map || method == .filter do
          throw s!"{file}: sort conditions in this callback need an element-restricted link lemma in {name}"
        let predicate := " ∧ ".intercalate (childConditions.map fun c => s!"({c})")
        let abstracted := s!"(fun ({param} : {elem.print names}) " ++
          " ".intercalate (scope.map fun (n, t) => s!"({n} : {t.print names})") ++ s!" => {predicate})"
        let applied := s!"({abstracted} x" ++ String.join (scope.map fun (n, _) => s!" {decode n}") ++ ")"
        let raw := s!"∀ _sortElement' ∈ ({items.print names}), ((fun ({param} : {elem.print names}) => {predicate}) _sortElement')"
        if parent.isSome then
          callbackConditions := callbackConditions ++ [(info.span, raw)]
        else if let some (_, _, _, loopInfo, _) := enclosingLoop then
          loopConditions := loopConditions ++ [(loopInfo.span, raw)]
        else
          let bindings := (leadingBindings outBody).filter fun (n, _) => info.scope.any fun (p, _) => p == n
          let mut available := outParams.map (·.1)
          for (n, value) in bindings do
            unless sortInputShape value && (sortInputNames value).all available.contains do
              throw s!"{file}: callback sort conditions must be reachable from parameters in {name}"
            available := n :: available
          -- Closed inputs, such as a literal array, also give a predicate
          -- whose free names are all parameters.
          unless sortInputShape items &&
              (sortInputNames items).all available.contains do
            throw s!"{file}: callback sort conditions must be reachable from parameters in {name}"
          let condition := "(" ++ String.join (bindings.map fun (n, e) => s!"let {n} := {e.print names}; ") ++ raw ++ ")"
          let hn := s!"{name}_sort_precondition{obligations.length}"
          if r.idents.contains hn then throw s!"{file}: reserved certificate hypothesis name {hn}"
          obligations := obligations ++ [(hn, condition)]
          inputConditions := inputConditions ++ [condition]
        let restricted := if method == .map then
          s!"evalMap_map_on fs {fuel} ρ {str param} _ {encX} {encY} {fn}"
          else s!"evalFilter_filter_on fs {fuel} ρ {str param} _ {encX} {fn}"
        let unpackKeys := hypNames.foldl (fun text h => text.replace s!"at {h} ⊢" s!"at {h} hkeys ⊢") unpack
        let vars := ("x", elem) :: scope.zipIdx.map fun ((_, t), i) => (s!"v{i}", t)
        let rewrites := if conditionalLemmas.isEmpty then "" else
          "  all_goals repeat' first\n" ++ String.join (conditionalLemmas.map fun lemma =>
            s!"    | rw [{lemma}]\n")
        loopLemmas := loopLemmas.push (r.cert lemmaName)
        conditionalLemmas := conditionalLemmas ++ [r.cert lemmaName]
        thms := thms.push <|
          s!"theorem {lemmaName} {functionGeneric} (fs : List (tolean.DeclRef × List String × tolean.TypeScript.IR.Body)){hfs}\n" ++
          s!"    (fuel : Nat) (ρ : Env {nv}){hI} (items : {itemsTy}) (hkeys : ∀ x ∈ items, {applied}) :\n" ++
          s!"    tolean.TypeScript.IR.Expr.{evalFn} fs {fuel} ρ {str param} ({term cbBody})\n" ++
          s!"      (List.map {encX} items) = some ({result}) := by\n" ++
          s!"  refine tolean.TypeScript.Proof.{restricted} items ?_\n" ++
          "  intro x hx\n" ++ substHfs ++ unpackKeys ++
          "  have hs := hkeys x hx\n" ++
          s!"  {casesOn decls vars}link_tac [{simpSet}, hs]\n" ++
          (if literalMaps.isEmpty then "" else s!"  all_goals (try simp only [{", ".intercalate literalMaps}, ← List.map_append])\n") ++
          rewrites ++
          s!"  all_goals (try simp_all [{simpSet}, hs])\n" ++
          "  all_goals first | assumption | rfl | (intros; rfl)\n"
        continue
      let vars := ("x", elem) :: scope.zipIdx.map fun ((_, t), i) => (s!"v{i}", t)
      loopLemmas := loopLemmas.push (r.cert lemmaName)
      thms := thms.push <|
        s!"theorem {lemmaName} {functionGeneric} (fs : List (tolean.DeclRef × List String × tolean.TypeScript.IR.Body)){hfs}\n" ++
        s!"    (fuel : Nat) (ρ : Env {nv}){hI} (items : {itemsTy}) :\n" ++
        s!"    tolean.TypeScript.IR.Expr.{evalFn} fs {fuel} ρ {str param}{indexArg} ({term cbBody}){want}{start}\n" ++
        s!"      (List.map {encX} items) = some ({result}) := by\n" ++
        s!"  refine tolean.TypeScript.Proof.{fromLemma} ?_ items\n" ++
        s!"  intro {intros}\n" ++ substHfs ++ unpack ++
        s!"  {casesOn decls vars}link_tac [{simpSet}]"
    let mut index := 0
    let mut returnsLoop := false
    for (stateNames, element, body, info, loopItems) in loopsOf outBody do
      index := index + 1
      let lemmaName := s!"{name}_loop{index}"
      if let .ext (.countUp k) [bound] := loopItems then
        let parameterNames := outParams.map (·.1)
        unless (sortInputNames bound).all parameterNames.contains do
          throw s!"{file}: counted loop bounds must read only function parameters in {name}"
        let hname := s!"{name}_counted_loop_precondition{obligations.length}"
        if r.idents.contains hname then throw s!"{file}: reserved certificate hypothesis name {hname}"
        let condition :=
          s!"({r.write "JSNumber.countUp?" "tolean.TypeScript.JSNumber.countUp?"} ({k} : _root_.Int) ({bound.print names})).isSome"
        obligations := obligations ++ [(hname, condition)]
        inputConditions := inputConditions ++ [condition]
      let parentLoop := parentLoopOf info.span
      let mut conditions := loopConditions.filterMap fun (span, condition) =>
        if span == info.span then some condition else none
      for (callee, (formals, calleeConditions)) in functionConditions do
        if calleeConditions.isEmpty then continue
        for (guards, actuals) in bodyConditionCalls callee body do
          let available := element :: info.scope.map (·.1)
          let ancestorState := (loopsOf outBody).flatMap fun (ns, _, b, _, _) =>
            if (loopsOf b).any (fun (_, _, _, child, _) => child.span == info.span) then ns else []
          unless actuals.length == formals.length &&
              guards.all (fun (n, _, _) => available.contains n && !ancestorState.contains n) &&
              actuals.all (fun e => (sortInputNames e).all available.contains &&
                !(sortInputNames e).any ancestorState.contains) do
            throw s!"{file}: a loop sort condition depends on changing state or body locals in {name}"
          callbackCalls := callee :: callbackCalls
          for (_, ty) in formals do
            let .list itemTy := ty | continue
            let some enc := encoderOf r itemTy | continue
            literalMaps := literalMaps ++ [s!"← List.map_singleton (f := {enc})",
              s!"← List.map_cons (f := {enc})"]
          for condition in calleeConditions do
            let binders := " ".intercalate (formals.map fun (p, t) => s!"({p} : {t.print names})")
            let arguments := " ".intercalate (actuals.map fun e => s!"({e.print names})")
            conditions := conditions ++ [guardCondition r guards s!"((fun {binders} => {condition}) {arguments})"]
      let restricted := !conditions.isEmpty
      if restricted then
        let outerScope := match parentLoop with
          | some (_, p, _, outerInfo, _) => (p, outerInfo.elem) :: outerInfo.scope
          | none => outParams
        if info.scope.any (fun (n, ty) => (outerScope.lookup n).any (fun outer => outer.print names != ty.print names)) then
          throw s!"{file}: sort conditions across an enclosing nullable narrowing need scope propagation in {name}"
      let some bodyStmt := loopBody syntaxBody info.span
        | throw s!"{file}: no loop at {info.span.start.line}:{info.span.start.col} in {name}"
      -- The loop lemma's rewrite does not reach a list of encoded lists yet,
      -- so a loop over arrays gets no certificate instead of one that fails.
      if (info.elem matches .list ..) && !restricted then
        throw s!"{file}: cannot certify a loop over arrays of arrays in {name} yet"
      let some encX := encoderOf r info.elem | throw s!"{file}: cannot encode the elements of a loop in {name}"
      let closures := (closureReads body).foldl (init := []) fun found entry =>
        if found.any (·.1 == entry.1) then found else found ++ [entry]
      let closures ← closures.mapM fun (n, value) => do
        let .ext (.closure params body) [] := value
          | throw s!"{file}: cannot state the closure invariant for {n}"
        pure (n, s!"{r.eval "Val.closure"} {list (params.map str)} {stmt body}")
      -- A step that ignores its element can also run over raw interpreter
      -- values, so callers need no codec for an irrelevant type parameter.
      let independentElement :=
        !(bodyNames body).contains element &&
        info.scope.all (fun (n, _) => !(bodyNames body).contains n) &&
        info.stateTypes.all (fun t => !tyHasParam t) &&
        closures.isEmpty && body.refs.isEmpty && (bodyCallbacks body).isEmpty &&
        !restricted && !info.breaks && info.returns.isNone
      let scope := info.scope
      let state := stateNames.zip info.stateTypes
      let vars := state ++ scope
      let coded ← vars.mapM fun (n, t) => do
        let (some e, some dec) := (encoderOf r t, decoderOf r t)
          | throw s!"{file}: cannot encode the variable {n} in {name}"
        return (n, e, dec)
      let decode (ρ n : String) : String :=
        match coded.find? (·.1 == n) with
        | some (_, _, dec) => s!"({dec} ({ρ}.lookup {str n}))"
        | none => "default"
      let predicate := " ∧ ".intercalate (conditions.map fun c => s!"({c})")
      let keyInvariant (ρ : String) : String :=
        let binders := " ".intercalate (info.scope.map fun (n, t) => s!"({n} : {t.print names})")
        let arguments := String.join (info.scope.map fun (n, _) => s!" {decode ρ n}")
        s!"∀ x ∈ items, ((fun ({element} : {info.elem.print names}) {binders} => {predicate}) x{arguments})"
      if restricted then
        let raw := s!"∀ _sortElement' ∈ ({loopItems.print names}), ((fun ({element} : {info.elem.print names}) => {predicate}) _sortElement')"
        if let some (outerState, _, _, outerInfo, _) := parentLoop then
          if (sortInputNames loopItems).any outerState.contains then
            throw s!"{file}: a nested sort condition depends on changing loop state in {name}"
          loopConditions := loopConditions ++ [(outerInfo.span, raw)]
        else
          let bindings := (leadingBindings outBody).filter fun (n, _) => info.scope.any fun (p, _) => p == n
          let mut available := outParams.map (·.1)
          for (n, e) in bindings do
            unless sortInputShape e && (sortInputNames e).all available.contains do
              throw s!"{file}: loop sort conditions must be reachable from parameters in {name}"
            available := n :: available
          unless sortInputShape loopItems && !(sortInputNames loopItems).isEmpty &&
              (sortInputNames loopItems).all available.contains do
            throw s!"{file}: loop sort conditions must be reachable from parameters in {name}"
          let condition := "(" ++ String.join (bindings.map fun (n, e) => s!"let {n} := {e.print names}; ") ++ raw ++ ")"
          let hn := s!"{name}_sort_precondition{obligations.length}"
          if r.idents.contains hn then throw s!"{file}: reserved certificate hypothesis name {hn}"
          obligations := obligations ++ [(hn, condition)]
          inputConditions := inputConditions ++ [condition]
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
        let shape := " ∧ ".intercalate ((coded.map fun (n, e, dec) =>
          s!"{ρ}.lookup {str n} = some ({e} ({dec} ({ρ}.lookup {str n})))") ++
          closures.map fun (n, value) =>
            s!"{ρ}.lookup {str n} = some ({value})")
        if restricted then s!"({shape}) ∧ ({keyInvariant ρ})" else shape
      let scopeNames := scope.map (·.1)
      let stepLines := IR.indentBy "        " (body.lines names)
      -- Every binder has its type, as in the output's loop (see `IR.foldBinders`).
      let captured := if scopeNames.isEmpty then "" else
        s!"fun {" ".intercalate (scope.map fun (n, t) => s!"({n} : {t.print names})")} => "
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
      let loopLemma := (if info.returns.isSome then "runFold_forInRet"
        else if info.breaks then "runFold_forIn" else "runFold_foldl") ++
        (if restricted then "_on" else "")
      let loopArgs := if info.returns.isSome then s!"{encX} {encR} {getRet} {getS} {init}" else encX
      let initProof := if info.returns.isSome then " (fun _ => ⟨rfl, rfl⟩)" else ""
      let stepNames := if info.returns.isSome then
          ["tolean.TypeScript.Proof.retOutcome", "ForInStep.value"]
        else if info.breaks then ["tolean.TypeScript.Proof.stepOutcome", "ForInStep.value"] else []
      if info.returns.isSome then returnsLoop := true
      let depth := if closures.isEmpty then callDepth m bodyStmt else callDepth m syntaxBody + closures.length
      let fuel := if depth == 0 then "fuel" else s!"(fuel + {depth})"
      -- A body with calls looks the functions up in the output, so the lemma
      -- is about the output's functions.
      let hfs := if depth == 0 then "" else s!" (hfs : fs = {outputFs})"
      let substHfs := if depth == 0 then "" else "    subst hfs\n"
      let hfsName := if depth == 0 then [] else [r.cert "decls"]
      -- `List (Option Int)`, with the parentheses that an element type needs.
      let itemsTy := (tolean.IR.Ty.list info.elem).print names
      let hypNames := (List.range (coded.length + closures.length)).map (s!"h{·}")
      -- `obtain h0 := hI` would lose the name, so one hypothesis gets a `have`.
      let bindHyps := if hypNames.length == 1 then "have h0 := hI"
        else "obtain ⟨" ++ ", ".intercalate hypNames ++ "⟩ := hI"
      let bindHyps := (if restricted then "obtain ⟨hI, hkeys⟩ := hI\n    " else "") ++ bindHyps
      let generalize (ρ : String) (which : List (String × String × String)) : String :=
        String.join (which.zipIdx.map fun ((n, _, dec), i) =>
          s!"    generalize {dec} ({ρ}.lookup {str n}) = v{i} at h{i}{if restricted then " hkeys" else ""} ⊢\n")
      let stateCoded := coded.take count
      let destruct := if count ≤ 1 then "" else
        s!"    obtain ⟨{", ".intercalate ((List.range count).map (s!"s{·}"))}⟩ := s\n"
      let closureLemmas := if closures.isEmpty then [] else ["tolean.TypeScript.Proof.lookup_ite"]
      let simpSet := ", ".intercalate (hfsName ++ stepNames ++ closureLemmas ++ envLemmas ++ lemmaNames.toList ++ codecLemmas ++
        loopLemmas.toList ++ defs)
      -- The values that one step sees: the element, the state, and the other
      -- locals, which the lemma generalizes to `v0`, `v1` and so on.
      let stateVars := if count ≤ 1 then ["s"].zip info.stateTypes
        else (List.range count).map (s!"s{·}") |>.zip info.stateTypes
      let loopVars := ("x", info.elem) :: stateVars ++ vars.zipIdx.map fun ((_, t), i) => (s!"v{i}", t)
      let rewrites := if !restricted || conditionalLemmas.isEmpty then "" else
        "    all_goals repeat' first\n" ++ String.join (conditionalLemmas.map fun lemma =>
          s!"      | rw [{lemma}]\n")
      loopLemmas := loopLemmas.push (r.cert lemmaName)
      if restricted then conditionalLemmas := conditionalLemmas ++ [r.cert lemmaName]
      thms := thms.push <|
        s!"theorem {lemmaName} {functionGeneric} (fs : List (tolean.DeclRef × List String × tolean.TypeScript.IR.Body)){hfs}\n" ++
        s!"    (fuel : Nat) (items : {itemsTy}) (ρ : Env {nv}) (hI : {inv "ρ"}) :\n" ++
        s!"    tolean.TypeScript.IR.Body.runFold fs {fuel} {list (stateNames.map str)} {str element}\n" ++
        s!"      ({term body}) ρ (List.map {encX} items) =\n" ++
        s!"      some {result "ρ"} := by\n" ++
        s!"  refine tolean.TypeScript.Proof.{loopLemma} fs {fuel} _ {str element} _ {loopArgs} (fun s ρ => {upd "s" "ρ"})\n" ++
        s!"    (fun ρ => {decState "ρ"}) (fun ρ => {stepFn "ρ"}) (fun ρ => {inv "ρ"}){initProof}" ++
        (if restricted then " items ?_ ?_ ρ hI\n" else " ?_ ?_ items ρ hI\n") ++
        s!"  · intro ρ s x hI{if restricted then " hx" else ""}\n" ++
        substHfs ++
        s!"    {bindHyps}\n    try simp only []\n" ++
        generalize "ρ" coded ++ destruct ++
        (if restricted then "    have hs := hkeys x hx\n" else "") ++
        s!"    {casesOn decls loopVars}link_tac [{simpSet}, {", ".intercalate hypNames}{if restricted then ", hs" else ""}]\n" ++
        (if !restricted || literalMaps.isEmpty then "" else
          s!"    all_goals (try simp only [{", ".intercalate literalMaps}, ← List.map_append])\n") ++
        rewrites ++
        (if restricted then s!"    all_goals (try simp_all [{simpSet}, hs])\n" ++
          s!"    all_goals (try link_tac [{simpSet}, hs, {", ".intercalate hypNames}])\n" ++
          "    all_goals first | assumption | rfl | (intros; rfl)\n" else "") ++
        s!"  · intro ρ hI\n" ++
        s!"    {bindHyps}\n    try simp only []\n" ++
        generalize "ρ" stateCoded ++
        -- With no locals in the state, the goal is `ρ = ρ`, which the step
        -- before may already close.
        s!"    all_goals simp [{", ".intercalate ((List.range count).map fun i => s!"Env.set_of_lookup _ _ _ h{i}")}]"
      if independentElement && count > 0 then
        let untypedName := s!"{lemmaName}_untyped"
        if r.idents.contains untypedName then
          throw s!"{file}: reserved certificate lemma name {untypedName}"
        let foldMapLemma := r.cert "foldl_map_encoded"
        unless lemmaNames.contains foldMapLemma do
          -- The interpreter folds encoded elements, but the translation folds
          -- source values. A step that ignores each element preserves the fold.
          encs := encs.push <|
            s!"theorem {foldMapLemma} \{α β σ : Type} (encode : α → β) (f : σ → α → σ) " ++
            s!"(g : σ → β → σ) (h : ∀ s x, g s (encode x) = f s x) (init : σ) (xs : List α) :\n" ++
            s!"    List.foldl g init (List.map encode xs) = List.foldl f init xs := by\n" ++
            "  induction xs generalizing init with\n" ++
            "  | nil => rfl\n" ++
            "  | cons x xs ih => simp only [List.map_cons, List.foldl_cons, h, ih]"
          lemmaNames := lemmaNames.push foldMapLemma
        let untypedCoded := coded.take count
        let untypedHypNames := (List.range count).map (s!"h{·}")
        let untypedBindHyps := if count == 1 then "have h0 := hI"
          else "obtain ⟨" ++ ", ".intercalate untypedHypNames ++ "⟩ := hI"
        let untypedInv (ρ : String) :=
          " ∧ ".intercalate (untypedCoded.map fun (n, e, dec) =>
            s!"{ρ}.lookup {str n} = some ({e} ({dec} ({ρ}.lookup {str n})))")
        let untypedStep (_ρ : String) :=
          s!"(fun ({IR.tuple stateNames} : {IR.foldState names info}) ({element} : Val {nv}) => (\n" ++
            "\n".intercalate stepLines ++ s!" : {stepTy}))"
        let untypedRun (ρ : String) :=
          s!"(List.foldl {untypedStep ρ} {decState ρ} items)"
        let untypedResult (ρ : String) :=
          s!"(.normal {upd (untypedRun ρ) ρ})"
        let untypedSimpSet := ", ".intercalate
          (envLemmas ++ lemmaNames.toList ++ untypedHypNames)
        loopLemmas := loopLemmas.push (r.cert untypedName)
        thms := thms.push <|
          s!"theorem {untypedName} {generic} (fs : List (tolean.DeclRef × List String × tolean.TypeScript.IR.Body))\n" ++
          s!"    (fuel : Nat) (items : List (Val {nv})) (ρ : Env {nv}) (hI : {untypedInv "ρ"}) :\n" ++
          s!"    tolean.TypeScript.IR.Body.runFold fs {fuel} {list (stateNames.map str)} {str element}\n" ++
          s!"      ({term body}) ρ items = some {untypedResult "ρ"} := by\n" ++
          s!"  suffices h : tolean.TypeScript.IR.Body.runFold fs {fuel} {list (stateNames.map str)} {str element}\n" ++
          s!"      ({term body}) ρ (List.map id items) = some {untypedResult "ρ"} by\n" ++
          "    simpa only [List.map_id] using h\n" ++
          s!"  refine tolean.TypeScript.Proof.runFold_foldl fs {fuel} _ {str element} _ id\n" ++
          s!"      (fun s ρ => {upd "s" "ρ"}) (fun ρ => {decState "ρ"}) (fun ρ => {untypedStep "ρ"})\n" ++
          s!"    (fun ρ => {untypedInv "ρ"}) ?_ ?_ items ρ hI\n" ++
          s!"  · intro ρ s x hI\n" ++
          s!"    {untypedBindHyps}\n    try simp only []\n" ++
          generalize "ρ" untypedCoded ++ destruct ++
          s!"    {casesOn decls stateVars}link_tac [{untypedSimpSet}, {", ".intercalate untypedHypNames}]\n" ++
          s!"  · intro ρ hI\n" ++
          s!"    {untypedBindHyps}\n    try simp only []\n" ++
          generalize "ρ" untypedCoded ++
          s!"    all_goals simp [{", ".intercalate ((List.range count).map fun i => s!"Env.set_of_lookup _ _ _ h{i}")}]"
    -- A direct forwarding call applies the callee's conditions to its actual
    -- arguments. Lambda binding avoids capturing names in those arguments.
    for callee in ((stmtsOf syntaxBody).flatMap stmtCalls).eraseDups do
      let (formals, conditions) := (functionConditions.lookup callee).getD ([], [])
      if conditions.isEmpty then continue
      let calls := bodyConditionCalls callee outBody
      let sourceCount := (((stmtsOf syntaxBody).flatMap stmtCalls).filter (· == callee)).length -
        (callbackCalls.filter (· == callee)).length
      unless calls.length == sourceCount do
        if hasTaggedConditionScope outBody then
          throw s!"{file}: a call with number-sort preconditions in unsupported tagged narrowing scope in {name}"
        throw s!"{file}: a call with number-sort preconditions inside a callback or unsupported scope in {name}"
      for (guards, actuals) in calls do
        unless actuals.length == formals.length do
          throw s!"{file}: missing argument for the sort precondition in {name}"
        unless guards.all (fun (n, _, _) => outParams.any (fun (p, _) => p == n)) &&
            (actuals.zip formals).all (fun (e, _, ty) =>
            (sortInputNames e).all (fun n => outParams.any (fun (p, _) => p == n)) &&
            (!(ty matches .list _) || (sortInputShape e && !(sortInputNames e).isEmpty))) do
          throw s!"{file}: a sort precondition needs arguments reachable from parameters in {name}"
        for (_, ty) in formals do
          let .list elem := ty | continue
          let some enc := encoderOf r elem | continue
          literalMaps := literalMaps ++ [s!"← List.map_singleton (f := {enc})",
            s!"← List.map_cons (f := {enc})", s!"← List.map_nil (f := {enc})"]
        for condition in conditions do
          let hname := s!"{name}_sort_precondition{obligations.length}"
          if r.idents.contains hname then
            throw s!"{file}: reserved certificate hypothesis name {hname}"
          let binders := " ".intercalate (formals.map fun (p, t) => s!"({p} : {t.print names})")
          let arguments := " ".intercalate (actuals.map fun e => s!"({e.print names})")
          let applied := guardCondition r guards s!"((fun {binders} => {condition}) {arguments})"
          obligations := obligations ++ [(hname, applied)]
          inputConditions := inputConditions ++ [applied]
    functionConditions := (name, (outParams, inputConditions)) :: functionConditions
    -- The encoders follow the types of the output, which the translator has
    -- already worked out from the source's types.
    let some retEnc := encoderOf r outRet | throw s!"{file}: cannot encode the result of {name}"
    let args ← outParams.mapM fun (p, t) => do
      let some e := encoderOf r t | throw s!"{file}: cannot encode the parameter {p}"
      return s!"({e} {p})"
    let binders := " ".intercalate (params.map fun p => s!"({p.name} : _)") ++
      String.join (obligations.map fun (n, p) => s!" ({n} : {p})")
    let call := " ".intercalate ((r.full s!"{transNs}.{name}" ++ callN) :: params.map (·.name))
    let retNames := if returnsLoop then ["tolean.TypeScript.Proof.retResult"] else []
    let simpSet := ", ".intercalate ([r.cert "decls"] ++ retNames ++ envLemmas ++ lemmaNames.toList ++ codecLemmas ++
      loopLemmas.toList ++ defs ++ obligations.map (·.1))
    let some_ := r.write "some" "Option.some"
    let rfl := r.full "rfl"
    let conditionRewrites := if conditionalLemmas.isEmpty then "" else
      "\n  all_goals repeat' first\n" ++ String.join (conditionalLemmas.map fun lemma =>
        s!"    | rw [{lemma}]\n") ++
      s!"  all_goals (try simp_all [{simpSet}])\n  all_goals first | assumption | rfl | (intros; first | rfl | simp_all)"
    thms := thms.push <|
      s!"theorem {name}_link {functionGeneric} {binders} :\n" ++
      s!"    {r.full "tolean.TypeScript.IR.runIn"} (N := {nv}) {outputFs} ⟨\"\", {str name}⟩ {list args} =\n" ++
      s!"      {some_} ({retEnc} ({call})) := by\n" ++
      s!"  {casesOn decls outParams}link_tac [{simpSet}]" ++
      (if literalMaps.isEmpty then "" else
        s!"\n  all_goals (try simp only [{", ".intercalate literalMaps}, ← List.map_append])\n" ++
        s!"  all_goals (try simp_all [{simpSet}, -List.map_cons, -List.map_nil, -List.map_map, ← List.map_append])") ++
      conditionRewrites ++
      -- After a loop that a `return` can end, the evaluator matches on the
      -- loop's outcome, which is itself a match on the value to return. Once
      -- that match is split, the arms for a `break` or a `continue` close, and
      -- the arm for the end of the loop reads the locals from its state.
      -- `link_eqs` relates the loop's result to the printed loop's, whose
      -- `match`es have other auxiliary functions.
      (if returnsLoop then
        "\n  all_goals (try split at *)\n  all_goals (subst_vars; link_eqs; simp_all [List.lookup])" else "")
    thms := thms.push <|
      s!"theorem {name}_cert {functionGeneric} {binders} :\n" ++
      s!"    {r.eval "run"} (N := {nv}) {r.cert "program"} {str name} {list args} = {some_} ({retEnc} ({call})) :=\n" ++
      s!"  {r.full "tolean.TypeScript.Proof.decls_sound"} {rfl} {rfl} {rfl} {r.cert "program_translated"} {str name} _ 64 _\n" ++
      s!"    ({" ".intercalate ([r.cert s!"{name}_link"] ++ functionCodecs.map (·.2) ++ params.map (·.name) ++ obligations.map (·.1))})"
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
    "-- A link theorem for a function with a nullable record parameter splits",
    "-- the record into every shape, and `link_tac` unfolds the evaluator in",
    "-- each. That can pass Lean's default budget.",
    "set_option maxHeartbeats 400000" ++
      (if hasClasses then "\nset_option maxRecDepth 100000" else ""),
    "",
    (if hasClasses then "/-- The program after ordinary-class elaboration. -/"
      else "/-- The program, as the parser read it. -/"),
    s!"def program : tolean.TypeScript.Syntax.Module :=\n  {module m}" ++ (if hasClasses then
      s!"\n\n/-- The original syntax, before class elaboration. -/\ndef parsedProgram : tolean.TypeScript.Syntax.Module :=\n  {module parsed}"
      else ""),
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
    s!"theorem program_parsed : tolean.TypeScript.Syntax.parseChars sourceChars .{target.name.toLower} = Except.ok {if hasClasses then "parsedProgram" else "program"} :=",
    "  tolean.TypeScript.Syntax.parseChars_eq_of_parsesTo (by decide +kernel)" ++ (if hasClasses then
      "\n\n/-- The kernel checks the elaboration result structurally. This is not a\n" ++
      "semantic-preservation theorem for the original JavaScript program. -/\n" ++
      s!"theorem program_elaborated : tolean.TypeScript.Elaborate.runChars sourceChars .{target.name.toLower} parsedProgram = Except.ok program := by\n" ++
      s!"  have hSource : (tolean.TypeScript.Elaborate.checkSource sourceChars .{target.name.toLower}).toBool = true := by decide +kernel\n" ++
      "  simp [tolean.TypeScript.Elaborate.runChars, parsedProgram, program,\n" ++
      "    tolean.TypeScript.Elaborate.checkSource_eq_of_checked hSource,\n" ++
      "    tolean.TypeScript.Elaborate.elaborateClass, tolean.TypeScript.Elaborate.constructors,\n" ++
      "    tolean.TypeScript.Elaborate.assignments, tolean.TypeScript.Elaborate.declaredFields,\n" ++
      "    tolean.TypeScript.Elaborate.methods, tolean.TypeScript.Elaborate.unique,\n" ++
      "    tolean.TypeScript.Elaborate.paramsEnv, tolean.TypeScript.Elaborate.expr,\n" ++
      "    tolean.TypeScript.Elaborate.receiver, tolean.TypeScript.Elaborate.stmt,\n" ++
      "    tolean.TypeScript.Elaborate.stmts, tolean.TypeScript.Elaborate.infer,\n" ++
      "    tolean.TypeScript.Elaborate.receiverClass, tolean.TypeScript.Elaborate.exactClass,\n" ++
      "    tolean.TypeScript.Elaborate.fields, tolean.TypeScript.Elaborate.classType,\n" ++
      "    tolean.TypeScript.Elaborate.ctorName, tolean.TypeScript.Elaborate.methodName,\n" ++
      "    tolean.TypeScript.Elaborate.generatedPrefix, tolean.TypeScript.Elaborate.thisName,\n" ++
      "    List.eraseDups_cons] <;> rfl"
      else ""),
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
  let m ← Elaborate.run source target m
  let all := m.decls.filterMap fun | .function _ _ n .. => some n | _ => none
  let fns := certifiable m
  return (fns, fns.length == all.length)

end tolean.TypeScript.Certify
