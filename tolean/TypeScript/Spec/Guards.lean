import tolean.TypeScript.Syntax.Ast

/-!
A predicate annotation has no runtime effect. A guard with one parameter
whose body returns a strict tag comparison computes that comparison, including
when its annotation lies. The interpreter expands only that syntactic shape.
The translator separately checks that its true set is the annotated type.

An expansion handles only a call on a plain identifier in an `if` test.
It keeps the call in a fresh binding, then tests the same tag inline. Keeping
the call makes the translator check its argument type and keeps its fuel cost.
The guard does not change its argument, so the second tag read is the same.
A parameter or any declaration in the caller that binds the guard's name prevents the
expansion. Local function bodies are left alone.
-/
namespace tolean.TypeScript.Eval

open tolean tolean.TypeScript.Syntax

structure GuardTest where
  parameter : String
  field : Option String
  tag : String
  equal : Bool

def GuardTest.expr (g : GuardTest) (s : Span) (name : String) : Expr :=
  .binary s (if g.equal then .strictEq else .strictNe)
    (match g.field with
      | some field => .member s (.ident s name) field
      | none => .unary s .typeof (.ident s name))
    (.string s g.tag)

def guardSide : Expr → Expr → Option (String × Option String × String)
  | .member _ (.ident _ name) field, .string _ tag => some (name, some field, tag)
  | .unary _ .typeof (.ident _ name), .string _ tag => some (name, none, tag)
  | _, _ => none

def returnsBool (b : Bool) : Stmt → Bool
  | .returnStmt _ (some (.bool _ value)) => value == b
  | .block _ [.returnStmt _ (some (.bool _ value))] => value == b
  | _ => false

def guardReturn : Stmt → Option Expr
  | .block _ [.returnStmt _ (some e)] => some e
  | .block _ [.ifStmt _ test t (some f)] =>
    if returnsBool true t && returnsBool false f then some test else none
  | _ => none

/-- The body returns just the comparison, directly or through two boolean
return branches, without statements before it. -/
def guardTest (params : List Param) (ret : Option TypeExpr) (body : Stmt) : Option GuardTest := do
  let [p] := params | none
  if p.optional then none else do
    let some (.predicate _ parameter _) := ret | none
    unless parameter == p.name do none
    let e ← guardReturn body
    let .binary _ op l r := e.stripParens | none
    unless op == .strictEq || op == .strictNe do none
    let (name, field, tag) ← guardSide l.stripParens r.stripParens <|>
      guardSide r.stripParens l.stripParens
    unless name == parameter do none
    return { parameter, field, tag, equal := op == .strictEq }

def guardTests (m : Module) : List (String × GuardTest) :=
  m.decls.filterMap fun
    | .function _ _ name _ params ret body => (guardTest params ret body).map (name, ·)
    | _ => none

def guardCondition (guards : List (String × GuardTest)) (test : Expr) : Option Expr :=
  match test.stripParens with
  | .call s (.ident _ name) [.ident a arg] =>
    match guards.lookup name with
    | some g => some (g.expr ⟨s.start, a.stop⟩ arg)
    | none => none
  | _ => none

/-- The apostrophe cannot occur in a source identifier. Positions distinguish
the calls within a function, as the hoister's counter distinguishes its names. -/
def guardBinding (s : Span) (test : Expr) : Stmt :=
  .varDecl s { kind := .const, name := s!"_guard{s.start.line}_{s.start.col}'", type := none, init := some test }

def GuardTest.body (g : GuardTest) (s : Span) : Stmt :=
  .block s [.ifStmt s (g.expr s g.parameter)
    (.returnStmt s (some (.bool s true))) (some (.returnStmt s (some (.bool s false))))]

/-- A strict comparison that reads just a tag and a string literal. -/
def pureTagTest (e : Expr) : Bool :=
  match e.stripParens with
  | .binary _ op l r => (op == .strictEq || op == .strictNe) &&
      ((guardSide l.stripParens r.stripParens).isSome || (guardSide r.stripParens l.stripParens).isSome)
  | _ => false

/-- Keep the calls of an else-if tag chain before its first match, so that
the printer can put the remaining tags in the same Lean match. These calls
only read tags. No statement or other kind of condition is crossed. -/
def guardChain (guards : List (String × GuardTest)) : Stmt → List (Span × Expr)
  | .ifStmt s test _ f =>
    if (guardCondition guards test).isSome then
      (s, test) :: (match f with | some b => guardChain guards b | none => [])
    else if pureTagTest test then
      match f with | some b => guardChain guards b | none => []
    else []
  | .block _ [b] => guardChain guards b
  | _ => []

mutual

def Stmt.expandGuards (guards : List (String × GuardTest)) (checked : List Span) : Stmt → Stmt
  | .ifStmt s test t f =>
    let calls := (guardChain guards (.ifStmt s test t f)).filter fun (sp, _) => !checked.contains sp
    let checked' := checked ++ calls.map (·.1)
    let t := Stmt.expandGuards guards checked' t
    let f := match f with | some b => some (Stmt.expandGuards guards checked' b) | none => none
    let result := .ifStmt s ((guardCondition guards test).getD test) t f
    if calls.isEmpty then result else .block s (calls.map (fun (sp, e) => guardBinding sp e) ++ [result])
  | .block s ss => .block s (Stmt.expandGuardsList guards checked ss)
  | .forOfStmt s k n e b => .forOfStmt s k n e (Stmt.expandGuards guards checked b)
  | .forOfPattern s k p e b => .forOfPattern s k p e (Stmt.expandGuards guards checked b)
  | .forStmt s d c u b => .forStmt s d c u (Stmt.expandGuards guards checked b)
  | .whileStmt s c b => .whileStmt s c (Stmt.expandGuards guards checked b)
  | .switchStmt s e cs => .switchStmt s e (Stmt.expandGuardsClauses guards checked cs)
  | s => s

def Stmt.expandGuardsList (guards : List (String × GuardTest)) (checked : List Span) : List Stmt → List Stmt
  | [] => []
  | .funDecl s name tps params ret body :: ss =>
    match guardTest params ret body with
    | some g =>
      .funDecl s name tps params ret (g.body body.span) ::
        Stmt.expandGuardsList ((name, g) :: guards.filter (·.1 != name)) checked ss
    | none =>
      .funDecl s name tps params ret body :: Stmt.expandGuardsList (guards.filter (·.1 != name)) checked ss
  | .ifStmt s test t f :: ss =>
    let calls := (guardChain guards (.ifStmt s test t f)).filter fun (sp, _) => !checked.contains sp
    let checked' := checked ++ calls.map (·.1)
    let t := Stmt.expandGuards guards checked' t
    let f := match f with | some b => some (Stmt.expandGuards guards checked' b) | none => none
    calls.map (fun (sp, e) => guardBinding sp e) ++
      .ifStmt s ((guardCondition guards test).getD test) t f :: Stmt.expandGuardsList guards checked ss
  | s :: ss => Stmt.expandGuards guards checked s :: Stmt.expandGuardsList guards checked ss

def Stmt.expandGuardsClauses (guards : List (String × GuardTest)) (checked : List Span) :
    List (Option Expr × List Stmt) → List (Option Expr × List Stmt)
  | [] => []
  | (e, ss) :: cs => (e, Stmt.expandGuardsList guards checked ss) :: Stmt.expandGuardsClauses guards checked cs

end

/-- Lower a guard's boolean result to the existing tag branch. At callers,
expand only names that cannot be hidden by a parameter or a declaration. -/
def guardedBody (guards : List (String × GuardTest)) (params : List Param)
    (ret : Option TypeExpr) (body : Stmt) : Stmt :=
  match guardTest params ret body with
  | some g => g.body body.span
  | none =>
    let visible := guards.filter fun (name, _) =>
      !(params.any (·.name == name)) && (body.binds name).isEmpty
    Stmt.expandGuards visible [] body

end tolean.TypeScript.Eval
