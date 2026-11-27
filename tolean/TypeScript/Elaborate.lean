import tolean.TypeScript.Syntax.Parser

/-!
Ordinary classes have no runtime tag in the readonly slice. This pass replaces
them with interfaces, object constructors and free functions before the
interpreter or the IR translator sees a module. It refuses operations that
could observe the class prototype.
-/
namespace tolean.TypeScript.Elaborate

open tolean Syntax

abbrev Result := Except String
abbrev Types := List (String × Option TypeExpr)

def refuse {α : Type} (s : Span) (message : String) : Result α :=
  .error s!"{s.start.line}:{s.start.col}: readonly classes: {message}"

def generatedPrefix : String := "__tolean_class_"
def ctorName (name : String) : String := s!"{generatedPrefix}{name.length}_{name}_new"
def methodName (name method : String) : String := s!"{generatedPrefix}{name.length}_{name}_method_{method}"
def thisName : String := generatedPrefix ++ "this"

def declaredFields (d : ClassDecl) : List Field :=
  d.members.filterMap fun | .field f => some f | _ => none

def fields (d : ClassDecl) : List Field :=
  (d.members.flatMap fun
    | .ctor ps _ => ps.filterMap fun p =>
      if p.readonly then p.param.type.map (fun t => ⟨p.param.span, true, p.param.name, false, t⟩)
      else none
    | _ => []) ++ declaredFields d

def methods (d : ClassDecl) : List ClassMethod :=
  d.members.filterMap fun | .method m => some m | _ => none

def constructors (d : ClassDecl) : List (List CtorParam × Stmt) :=
  d.members.filterMap fun | .ctor ps b => some (ps, b) | _ => none

structure Context where
  classes : List ClassDecl
  aliases : List (String × TypeExpr)
  returns : Types
  self : Option ClassDecl := none
  expectedReturn : Option TypeExpr := none

def classType (d : ClassDecl) : TypeExpr := .ref d.span d.name []

def exactClassFuel (ctx : Context) : Nat → TypeExpr → Option ClassDecl
  | 0, _ => none
  | fuel + 1, .ref _ name [] =>
    match ctx.classes.find? (·.name == name) with
    | some d => some d
    | none => (ctx.aliases.lookup name).bind (exactClassFuel ctx fuel)
  | fuel + 1, .paren _ t => exactClassFuel ctx fuel t
  | _, _ => none

def exactClass (ctx : Context) (ty : TypeExpr) : Option ClassDecl :=
  exactClassFuel ctx 8 ty

def containsClassTypeFuel (ctx : Context) : Nat → TypeExpr → Bool
  | 0, _ => true
  | fuel + 1, ty =>
    if (exactClassFuel ctx fuel ty).isSome then true else
    match ty with
    | .ref _ name args =>
      (ctx.aliases.lookup name).any (containsClassTypeFuel ctx fuel) ||
        args.any (containsClassTypeFuel ctx fuel)
    | .array _ inner | .paren _ inner => containsClassTypeFuel ctx fuel inner
    | .union _ members => members.any (containsClassTypeFuel ctx fuel)
    | .tuple _ _ elems => elems.any (containsClassTypeFuel ctx fuel)
    | .object _ fs => fs.any fun
      | .field _ _ _ _ fieldTy => containsClassTypeFuel ctx fuel fieldTy
    | .predicate _ _ target => containsClassTypeFuel ctx fuel target
    | _ => false

def paramsEnv (params : List Param) : Types := params.map fun p => (p.name, p.type)

def infer (ctx : Context) (env : Types) : Nat → Expr → Option TypeExpr
  | 0, _ => none
  | f + 1, e =>
    match e with
    | .ident _ name => (env.lookup name).join
    | .this _ => ctx.self.map classType
    | .new s name _ _ => some (.ref s name [])
    | .paren _ e | .asConst _ e | .satisfies _ e _ => infer ctx env f e
    | .call _ (.ident _ name) _ =>
      if env.any (·.1 == name) then none else (ctx.returns.lookup name).join
    | .call _ (.member _ recv name) _ => do
      let ty ← infer ctx env f recv
      let d ← exactClass ctx ty
      let m ← (methods d).find? (·.name == name)
      m.returnType
    | .member _ recv name => do
      let ty ← infer ctx env f recv
      let d ← exactClass ctx ty
      let field ← (fields d).find? (·.name == name)
      pure field.type
    | .number s _ => some (.keyword s "number")
    | .bigint s _ => some (.keyword s "bigint")
    | .string s _ => some (.keyword s "string")
    | .bool s _ => some (.keyword s "boolean")
    | _ => none

def receiverClass (ctx : Context) (env : Types) (recv : Expr) : Option ClassDecl :=
  (infer ctx env 1000 recv).bind (exactClass ctx)

def constructedClass (ctx : Context) : Expr → Option ClassDecl
  | .new _ name [] _ => ctx.classes.find? (·.name == name)
  | _ => none

def hasClassType (ctx : Context) (ty : Option TypeExpr) : Bool :=
  ty.any (containsClassTypeFuel ctx 8)

def directClassType (ctx : Context) (ty : Option TypeExpr) : Option ClassDecl :=
  ty.bind (exactClass ctx)

def checkClassBinding (ctx : Context) (s : Span) (d : VarDecl) : Result Unit := do
  if hasClassType ctx d.type then
    let some init := d.init
      | refuse s "class-typed locals must be initialized from a constructed class instance"
    let some expected := d.type
      | refuse s "class-typed locals need an explicit type"
    let some cls := exactClass ctx expected
      | refuse s "class-typed local aliases must resolve to one class"
    unless (constructedClass ctx init).any (·.name == cls.name) do
      refuse s "class-typed locals must be initialized directly with new for the declared class"

mutual

def expr (ctx : Context) (env : Types) : Nat → Expr → Result Expr
  | 0, e => refuse e.span "elaboration exceeded its nesting budget"
  | f + 1, e => do
    match e with
    | .this s => refuse s "'this' may occur only as a direct field or method receiver; it may not escape"
    | .ident s name =>
      if ctx.classes.any (·.name == name) then
        refuse s "class constructor identity and static properties are not supported"
      else pure e
    | .new s name ts args =>
      let args' ← args.mapM (expr ctx env f)
      if ctx.classes.any (·.name == name) then
        if env.any (·.1 == name) then refuse s "class constructors may not be shadowed"
        unless ts.isEmpty do refuse s "generic classes are not supported"
        pure (.call s (.ident s (ctorName name)) args')
      else pure (.new s name ts args')
    | .call s (.member ms recv name) args =>
      match receiverClass ctx env recv with
      | some d =>
        unless (methods d).any (·.name == name) do
          refuse ms "only a declared method can be called on a class instance"
        let recv' ← receiver ctx env f recv
        pure (.call s (.ident ms (methodName d.name name))
          (recv' :: (← args.mapM (expr ctx env f))))
      | none =>
        -- The ordinary checker handles receivers without an exact class type.
        -- Lowered class interfaces have no methods, so this cannot add dispatch.
        pure (.call s (.member ms (← expr ctx env f recv) name) (← args.mapM (expr ctx env f)))
    | .call s callee args =>
      pure (.call s (← expr ctx env f callee) (← args.mapM (expr ctx env f)))
    | .member s recv name =>
      if name == "constructor" then refuse s "constructor property identity is not supported"
      let recv' ← receiver ctx env f recv
      if let some d := receiverClass ctx env recv then
        if (methods d).any (·.name == name) then refuse s "class methods may not be extracted as values"
        unless (fields d).any (·.name == name) do refuse s "class instances expose only their readonly fields"
      pure (.member s recv' name)
    | .index s recv key | .optIndex s recv key =>
      if (receiverClass ctx env recv).isSome then refuse s "computed class properties are not supported"
      match e with
      | .index .. => pure (.index s (← expr ctx env f recv) (← expr ctx env f key))
      | _ => pure (.optIndex s (← expr ctx env f recv) (← expr ctx env f key))
    | .optMember s recv name =>
      if (receiverClass ctx env recv).isSome || name == "constructor" then
        refuse s "optional class property access and method dispatch are not supported"
      pure (.optMember s (← expr ctx env f recv) name)
    | .binary s .instanceof _ _ => refuse s "'instanceof' is not supported by the ordinary-class desugaring"
    | .binary s op a b => pure (.binary s op (← expr ctx env f a) (← expr ctx env f b))
    | .assign s op target value =>
      match target with
      | .ident _ name =>
        if ((env.lookup name).join.bind (exactClass ctx)).isSome then
          refuse s "class-typed locals may not be reassigned"
      | _ =>
        if (infer ctx env 1000 target).isSome then
          refuse s "class fields are readonly"
      pure (.assign s op (← expr ctx env f target) (← expr ctx env f value))
    | .array s es => pure (.array s (← es.mapM (expr ctx env f)))
    | .object s ps => pure (.object s (← ps.mapM (property ctx env f)))
    | .paren s e => pure (.paren s (← expr ctx env f e))
    | .unary s op e => pure (.unary s op (← expr ctx env f e))
    | .prefix s op e => pure (.prefix s op (← expr ctx env f e))
    | .postfix s op e => pure (.postfix s op (← expr ctx env f e))
    | .cond s t a b => pure (.cond s (← expr ctx env f t) (← expr ctx env f a) (← expr ctx env f b))
    | .arrow s parens ps body =>
      if ps.any (fun p => hasClassType ctx p.type) then
        refuse s "source functions may not accept class-typed parameters because callers could pass plain objects"
      pure (.arrow s parens ps (← expr ctx (paramsEnv ps ++ env) f body))
    | .asConst s e => pure (.asConst s (← expr ctx env f e))
    | .satisfies s e t => pure (.satisfies s (← expr ctx env f e) t)
    | .spread s e =>
      if (receiverClass ctx env e).isSome then refuse s "spreading class instances is not supported"
      pure (.spread s (← expr ctx env f e))
    | _ => pure e

def receiver (ctx : Context) (env : Types) (fuel : Nat) (e : Expr) : Result Expr :=
  match e, ctx.self with
  | .this s, some _ => pure (.ident s thisName)
  | _, _ => expr ctx env fuel e

def property (ctx : Context) (env : Types) (fuel : Nat) : Property → Result Property
  | .shorthand s name => do
    let e ← expr ctx env fuel (.ident s name)
    pure (.keyValue s (.ident name) e)
  | .keyValue s key e => do pure (.keyValue s key (← expr ctx env fuel e))
  | .spread s e => do
    if (receiverClass ctx env e).isSome then refuse s "spreading class instances is not supported"
    pure (.spread s (← expr ctx env fuel e))

end

def bindingType (ctx : Context) (env : Types) (d : VarDecl) : Option TypeExpr :=
  d.type.orElse fun _ => d.init.bind (infer ctx env 1000)

mutual

def stmt (ctx : Context) (env : Types) : Nat → Stmt → Result Stmt
  | 0, s => refuse s.span "elaboration exceeded its nesting budget"
  | f + 1, st => do
    match st with
    | .varDecl s d =>
      checkClassBinding ctx s d
      pure (.varDecl s { d with init := ← d.init.mapM (expr ctx env f) })
    | .returnStmt s e => do
      if let some expected := ctx.expectedReturn then
        if let some d := exactClass ctx expected then
          let some value := e
            | refuse s "a class-typed function must return a constructed class instance"
          unless (constructedClass ctx value).any (·.name == d.name) do
            refuse s "a class-typed function must return new for the declared class, not an object or copy"
      pure (.returnStmt s (← e.mapM (expr ctx env f)))
    | .exprStmt s e => pure (.exprStmt s (← expr ctx env f e))
    | .block s ss => pure (.block s (← stmts ctx env f ss))
    | .ifStmt s t a b =>
      pure (.ifStmt s (← expr ctx env f t) (← stmt ctx env f a) (← b.mapM (stmt ctx env f)))
    | .throwStmt s e => pure (.throwStmt s (← expr ctx env f e))
    | .tryCatch s body name handler =>
      pure (.tryCatch s (← stmt ctx env f body) name
        (← stmt ctx ((name, some (.keyword s "unknown")) :: env) f handler))
    | .whileStmt s t b => pure (.whileStmt s (← expr ctx env f t) (← stmt ctx env f b))
    | .forStmt s init test update body =>
      let env' := match init with | some d => (d.name, bindingType ctx env d) :: env | none => env
      init.forM fun d => checkClassBinding ctx s d
      let init' ← init.mapM fun d => do
        pure { d with init := ← d.init.mapM (expr ctx env f) }
      pure (.forStmt s init' (← test.mapM (expr ctx env' f)) (← update.mapM (expr ctx env' f))
        (← stmt ctx env' f body))
    | .forOfStmt s k n items body =>
      let ty := match infer ctx env 1000 items with
        | some (.array _ t) => some t
        | _ => none
      pure (.forOfStmt s k n (← expr ctx env f items) (← stmt ctx ((n, ty) :: env) f body))
    | .forOfPattern s k p items body =>
      pure (.forOfPattern s k p (← expr ctx env f items)
        (← stmt ctx (p.names.map (·, none) ++ env) f body))
    | .destructure s k p ty e => pure (.destructure s k p ty (← expr ctx env f e))
    | .objectDestructure s k p ty e =>
      pure (.objectDestructure s k p ty (← expr ctx env f e))
    | .switchStmt s e clauses =>
      pure (.switchStmt s (← expr ctx env f e) (← clauses.mapM fun (test, body) => do
        pure (← test.mapM (expr ctx env f), ← stmts ctx env f body)))
    | .funDecl s name tps ps rt body =>
      if ps.any (fun p => hasClassType ctx p.type) then
        refuse s "source functions may not accept class-typed parameters because callers could pass plain objects"
      if hasClassType ctx rt && (directClassType ctx rt).isNone then
        refuse s "functions may not return class instances inside containers because their provenance cannot be checked"
      pure (.funDecl s name tps ps rt
        (← stmt { ctx with self := none, expectedReturn := rt } (paramsEnv ps ++ env) f body))
    | .breakStmt _ | .continueStmt _ | .empty _ => pure st

def stmts (ctx : Context) (env : Types) (fuel : Nat) : List Stmt → Result (List Stmt)
  | [] => pure []
  | s :: ss => do
    let s' ← stmt ctx env fuel s
    let env' := match s with
      | .varDecl _ d => (d.name, bindingType ctx env d) :: env
      | .destructure _ _ p _ _ => p.names.map (·, none) ++ env
      | .objectDestructure _ _ p _ _ => p.objectBindingNames.map (·, none) ++ env
      | .funDecl _ name _ _ _ _ => (name, none) :: env
      | .exprStmt .. | .returnStmt .. | .ifStmt .. | .forOfStmt .. | .forOfPattern ..
      | .forStmt .. | .whileStmt .. | .block .. | .breakStmt _ | .continueStmt _ | .empty _
      | .switchStmt .. | .throwStmt .. | .tryCatch .. => env
    pure (s' :: (← stmts ctx env' fuel ss))

end

def unique (s : Span) (what : String) (names : List String) : Result Unit := do
  unless names.eraseDups.length == names.length do refuse s s!"duplicate {what} are not supported"

def assignments (s : Span) : List Stmt → Result (List (String × Expr))
  | [] => pure []
  | .empty _ :: ss => assignments s ss
  | .exprStmt _ (.assign _ .assign (.member _ (.this _) name) value) :: ss => do
    pure ((name, value) :: (← assignments s ss))
  | _ => refuse s "a constructor body must assign each readonly field once; other constructor statements are not supported"

def elaborateClass (ctx : Context) (d : ClassDecl) : Result (List Decl) := do
  let [(cps, body)] := constructors d
    | refuse d.span "an ordinary class must declare exactly one constructor"
  let .block _ ss := body | refuse d.span "a constructor needs a block body"
  let assigned ← assignments d.span ss
  let parameterFields ← cps.filterMapM fun p => do
    if hasClassType ctx p.param.type then
      refuse p.param.span "constructors may not accept class-typed parameters because callers could pass plain objects"
    if !p.readonly then return none
    let some type := p.param.type
      | refuse p.param.span "a readonly constructor parameter needs a type"
    return some (⟨p.param.span, true, p.param.name, false, type⟩ : Field)
  let fs := parameterFields ++ declaredFields d
  let ms := methods d
  unique d.span "field or method names" (fs.map (·.name) ++ ms.map (·.name))
  unique d.span "constructor assignments" (assigned.map Prod.fst)
  for f in fs do
    if hasClassType ctx (some f.type) && (exactClass ctx f.type).isNone then
      refuse f.span "class instances inside field containers are not supported"
    if f.name == "constructor" || f.name == "__proto__" then
      refuse f.span "constructor and __proto__ fields are not supported"
    unless f.readonly && !f.optional do refuse f.span "fields must be required and readonly"
  unless (assigned.map Prod.fst).all (fun n => (declaredFields d).any (·.name == n)) &&
      (declaredFields d).all (fun f => (assigned.map Prod.fst).contains f.name) do
    refuse d.span "the constructor must assign every declared field exactly once and no undeclared field"
  let ps ← cps.mapM fun p => do
    if p.param.optional then refuse p.param.span "optional constructor parameters are not supported"
    let ty := p.param.type.orElse fun _ =>
      (assigned.findSome? fun (name, value) =>
        match value with
        | .ident _ n => if n == p.param.name then (fs.find? (·.name == name)).map (·.type) else none
        | _ => none)
    let some ty := ty | refuse p.param.span "a constructor parameter needs a type or a direct assignment to a typed field"
    pure { p.param with type := some ty }
  unique d.span "constructor parameter names" (ps.map (·.name))
  let env := paramsEnv ps
  let bindings ← assigned.zipIdx |>.mapM fun ((name, value), index) => do
    let some field := fs.find? (·.name == name)
      | refuse value.span "unknown constructor field"
    if let some fieldClass := exactClass ctx field.type then
      unless (constructedClass ctx value).any (·.name == fieldClass.name) do
        refuse value.span "class-typed fields must receive new for the declared class, not an object or copy"
    let temp := s!"{generatedPrefix}field_{index}"
    let value' ← expr { ctx with self := none } env 1000 value
    pure (name, temp, Stmt.varDecl value.span ⟨.const, temp, some field.type, some value'⟩)
  let props := fs.map fun field =>
    let value := match bindings.find? (fun b => b.1 == field.name) with
      | some b => Expr.ident field.span b.2.1
      | none => Expr.ident field.span field.name
    Property.keyValue field.span (.ident field.name) value
  let ctor := Decl.function d.span false (ctorName d.name) [] ps (some (classType d))
    (.block d.span (bindings.map (·.2.2) ++ [.returnStmt d.span (some (.object d.span props))]))
  let methodDecls ← ms.mapM fun m => do
    if m.params.any (fun p => hasClassType ctx p.type) then
      refuse m.span "methods may not accept class-typed parameters because callers could pass plain objects"
    if hasClassType ctx m.returnType && (directClassType ctx m.returnType).isNone then
      refuse m.span "methods may not return class instances inside containers because their provenance cannot be checked"
    unique m.span "method parameter names" (m.params.map (·.name))
    let selfParam : Param := ⟨m.span, thisName, false, some (classType d)⟩
    let body' ← stmt { ctx with self := some d, expectedReturn := m.returnType }
      (paramsEnv m.params) 1000 m.body
    pure (Decl.function m.span false (methodName d.name m.name) []
      (selfParam :: m.params) m.returnType body')
  pure (.interface d.span d.exported d.name [] fs :: ctor :: methodDecls)

/-- Check hygiene separately so certificates can reduce this small computation
without reducing the elaboration of all class bodies at the same time. -/
def checkSource (chars : List Char) (target : Edition) : Result Unit := do
  let tokens ← (Syntax.lexChars chars target).mapError (fun e => e.message)
  for t in tokens do
    if let .ident name := t.kind then
      if name.startsWith generatedPrefix then
        refuse t.span s!"source names beginning with '{generatedPrefix}' are reserved"
  pure ()

theorem checkSource_eq_of_checked {chars : List Char} {target : Edition}
    (h : (checkSource chars target).toBool = true) : checkSource chars target = .ok () := by
  cases he : checkSource chars target with
  | error e => simp [he, Except.toBool] at h
  | ok u => cases u; rfl

/-- Programs without ordinary classes keep their existing path. The reserved
prefix makes generated binders fresh even inside nested source expressions. -/
def runChars (chars : List Char) (target : Edition) (m : Module) : Result Module := do
  let classes := m.decls.filterMap fun | .classDecl d => some d | _ => none
  if classes.isEmpty then return m
  checkSource chars target
  let first :: _ := classes | return m
  unique first.span "class names" (classes.map (·.name))
  for decl in m.decls do
    let names := match decl with
      | .function _ _ name _ _ _ _ => [name]
      | .exportedVar _ d => [d.name]
      | .import _ names _ => names.filterMap fun (n : ImportName) => if n.typeOnly then none else some n.binding
      | _ => []
    if names.any (fun name => classes.any (·.name == name)) then
      refuse decl.span "class names may not share a runtime binding with another declaration"
  let returns := m.decls.filterMap fun
    | .function _ _ name _ _ rt _ => some (name, rt)
    | _ => none
  let aliases := m.decls.filterMap fun
    | .typeAlias _ _ name [] ty => some (name, ty)
    | _ => none
  let ctx : Context := ⟨classes, aliases, returns, none, none⟩
  let decls ← m.decls.flatMapM fun
    | .classDecl d => elaborateClass ctx d
    | .function s exported name tps ps rt body => do
      if ps.any (fun p => hasClassType ctx p.type) then
        refuse s "source functions may not accept class-typed parameters because callers could pass plain objects"
      if hasClassType ctx rt && (directClassType ctx rt).isNone then
        refuse s "functions may not return class instances inside containers because their provenance cannot be checked"
      let body' ← stmt { ctx with expectedReturn := rt } (paramsEnv ps) 1000 body
      pure [.function s exported name tps ps rt body']
    | .stmt s => do pure [Decl.stmt (← stmt ctx [] 1000 s)]
    | .exportedVar s d => do
      if hasClassType ctx d.type then
        let some init := d.init
          | refuse s "class-typed values must be initialized from a constructed class instance"
        let some expected := d.type
          | refuse s "class-typed values need an explicit type"
        let some cls := exactClass ctx expected
          | refuse s "class-typed aliases must resolve to one class"
        unless (constructedClass ctx init).any (·.name == cls.name) do
          refuse s "class-typed values must be initialized directly with new for the declared class"
      pure [.exportedVar s { d with init := ← d.init.mapM (expr ctx [] 1000) }]
    | d => pure [d]
  pure ⟨decls⟩

def run (source : String) (target : Edition) (m : Module) : Result Module :=
  runChars source.toList target m

end tolean.TypeScript.Elaborate
