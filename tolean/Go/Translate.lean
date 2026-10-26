import tolean.Go.Syntax.Parser

/-!
The Go translator. It reads the files of one Go package, keeps the root
functions and the declarations they reach, and writes them as Lean
definitions over the model in `tolean/Go/Spec/Basic.lean`.

- A function that calls a method on an interface parameter, such as a store,
  becomes a function in `StateM State`. The interface becomes a structure of the
  methods the code calls, each a step in `StateM State`, so a model of the store
  can be plugged in later.
- A `range` loop becomes its own recursive function over the list.
  `continue` is the recursive call, `break` returns the locals that the loop
  changes, and `return` leaves the function with its result.
- `int` and `int64` arithmetic wraps as Go's does, through `Go.wrap64`.
- Code that only feeds observability, such as tracing and timing, is erased:
  statements that read a value of an erased type or call an erased package.
  An erased statement may only assign through the erased value, so erasing it
  cannot change any other value.

Everything else is refused with a position and a reason.
-/
namespace tolean.Go.Translate

open tolean tolean.Go.Syntax

/-! ## Types -/

inductive Ty where
  | int
  | bool
  | string
  | byte
  | named (name : String)
  | slice (elem : Ty)
  | array (len : Nat) (elem : Ty)
  | error
  | context
  /-- A value that the translation erases. -/
  | erased
  | nil
  | tuple (items : List Ty)
deriving BEq, Inhabited, Repr

structure Config where
  roots : List String
  /-- Named types whose values are erased, such as a trace collector. -/
  eraseTypes : List String
  /-- Packages whose calls are erased, such as `time`. -/
  erasePackages : List String

structure FuncDef where
  file : String
  name : String
  /-- The receiver's name and type name, for a method. -/
  recv : Option (String × String)
  params : List (String × Expr)
  results : List Expr
  body : Stmt
  span : Span

structure TypeDef where
  file : String
  name : String
  type : Expr
  alias : Bool

structure ValueDef where
  file : String
  name : String
  keyword : String
  type : Option Expr
  value : Option Expr
  span : Span

structure Pkg where
  name : String
  types : List TypeDef := []
  funcs : List FuncDef := []
  values : List ValueDef := []

structure Local where
  go : String
  lean : String
  ty : Ty
deriving Inhabited

/-- What `return`, `break` and `continue` mean where a statement stands. -/
inductive Mode where
  | top
  /-- In the body of the loop function `name`. `fixed` are the arguments
  passed unchanged, `next` the index and list for the next iteration, and
  `written` the loop's changing locals. -/
  | loop (name : String) (fixed : List String) (next : String) (written : List Local)

structure TState where
  pkg : Pkg
  cfg : Config
  file : String := ""
  scopes : List (List Local) := [[]]
  used : List String := []
  mutNames : List String := []
  aux : Array String := #[]
  loopCount : Nat := 0
  fnName : String := ""
  effectful : List String := []
  /-- The interface methods the translated code calls. -/
  methods : List (String × String) := []
  inEffectful : Bool := false
  /-- The state type parameter of effectful functions: `State`, or a fresh
  name when the package uses `State`. -/
  stateVar : String := "State"
  results : List Ty := []

abbrev TM := StateT TState (Except String)

def fail {A : Type} (span : Span) (message : String) : TM A := do
  let s ← get
  throw s!"{s.file}:{span.start.line}:{span.start.col}: {message}"

/-! ## Names -/

def leanKeywords : List String :=
  ["at", "by", "do", "then", "else", "if", "match", "with", "let", "have", "show", "from",
   "in", "fun", "end", "open", "namespace", "section", "return", "mut", "for", "unless",
   "where", "instance", "structure", "class", "theorem", "def", "axiom", "variable",
   "universe", "Type", "Prop", "Sort", "import", "deriving", "extends", "calc", "try",
   "catch", "finally", "break", "continue", "nomatch", "nofun", "macro", "syntax", "local",
   "private", "protected", "partial", "unsafe", "noncomputable", "example", "abbrev",
   "opaque", "inductive", "export", "attribute", "notation", "this", "rest", "pure"]

def leanName (n : String) : String := if leanKeywords.contains n then s!"«{n}»" else n

/-! ## Reading the package -/

def fieldNames (fields : List Field) : List (String × Expr) :=
  fields.flatMap fun
    | .mk _ [] ty _ => [("_", ty)]
    | .mk _ names ty _ => names.map (·, ty)

def typeNameOf : Expr → Option String
  | .ident _ n => some n
  | .star _ (.ident _ n) => some n
  | _ => none

def readPkg (files : List (String × File)) : Except String Pkg := do
  let mut pkg : Pkg := { name := (files.head?.map (·.2.package)).getD "" }
  for (path, f) in files do
    for d in f.decls do
      match d with
      | .func span recv name params results body =>
        let recv? := match recv with
          | some [.mk _ [r] ty _] => (typeNameOf ty).map (r, ·)
          | some [.mk _ [] ty _] => (typeNameOf ty).map ("_", ·)
          | _ => none
        let fname := match recv? with
          | some (_, t) => s!"{t}.{name}"
          | none => name
        pkg := { pkg with funcs := pkg.funcs ++ [{
          file := path, name := fname, recv := recv?, params := fieldNames params,
          results := ((results.getD []).flatMap fun
            | .mk _ [] ty _ => [ty]
            | .mk _ names ty _ => names.map fun _ => ty),
          body, span }] }
      | .gen (.mk _ kw specs) =>
        for spec in specs do
          match spec with
          | .type _ name ty alias =>
            pkg := { pkg with types := pkg.types ++ [{ file := path, name, type := ty, alias }] }
          | .value span names ty values =>
            for (n, i) in names.zipIdx do
              pkg := { pkg with values := pkg.values ++ [{
                file := path, name := n, keyword := kw, type := ty, value := values[i]?, span }] }
          | .import .. => pure ()
  return pkg

/-! ## Walking the syntax tree -/

mutual

partial def exprIdents : Expr → List String
  | .ident _ n => [n]
  | .lit .. => []
  | .composite _ ty elts => (ty.map exprIdents).getD [] ++ elts.flatMap exprIdents
  | .keyValue _ k v => exprIdents k ++ exprIdents v
  | .paren _ e | .star _ e | .unary _ _ e | .sliceType _ e | .ellipsis _ e => exprIdents e
  | .selector _ e n => n :: exprIdents e
  | .index _ a b | .binary _ _ a b | .arrayType _ a b | .mapType _ a b =>
    exprIdents a ++ exprIdents b
  | .sliceExpr _ e lo hi => exprIdents e ++ (lo.map exprIdents).getD [] ++ (hi.map exprIdents).getD []
  | .call _ f args _ => exprIdents f ++ args.flatMap exprIdents
  | .structType _ fs | .interfaceType _ fs => fs.flatMap fieldIdents
  | .funcType _ ps rs => ps.flatMap fieldIdents ++ (rs.getD []).flatMap fieldIdents
  | .typeAssert _ e t => exprIdents e ++ (t.map exprIdents).getD []
  | .funcLit _ t b => exprIdents t ++ stmtIdents b

partial def fieldIdents : Field → List String
  | .mk _ _ ty tag => exprIdents ty ++ (tag.map exprIdents).getD []

partial def stmtIdents : Stmt → List String
  | .block _ ss => ss.flatMap stmtIdents
  | .expr _ e | .deferStmt _ e => exprIdents e
  | .assign _ _ l r => l.flatMap exprIdents ++ r.flatMap exprIdents
  | .incDec _ _ e => exprIdents e
  | .decl _ (.mk _ _ specs) => specs.flatMap fun
    | .value _ _ t vs => (t.map exprIdents).getD [] ++ vs.flatMap exprIdents
    | .type _ _ t _ => exprIdents t
    | .import .. => []
  | .ret _ es => es.flatMap exprIdents
  | .brk _ | .cont _ => []
  | .ifStmt _ i c b e =>
    (i.map stmtIdents).getD [] ++ exprIdents c ++ stmtIdents b ++ (e.map stmtIdents).getD []
  | .forStmt _ i c p b =>
    (i.map stmtIdents).getD [] ++ (c.map exprIdents).getD [] ++ (p.map stmtIdents).getD [] ++
      stmtIdents b
  | .range _ _ k v x b =>
    (k.map exprIdents).getD [] ++ (v.map exprIdents).getD [] ++ exprIdents x ++ stmtIdents b
  | .switchStmt _ i t _ cs =>
    (i.map stmtIdents).getD [] ++ (t.map exprIdents).getD [] ++ cs.flatMap caseIdents
  | .typeSwitch _ i g _ cs => (i.map stmtIdents).getD [] ++ stmtIdents g ++ cs.flatMap caseIdents

partial def caseIdents : CaseClause → List String
  | .mk _ es body => (es.getD []).flatMap exprIdents ++ body.flatMap stmtIdents

end

/-- Every name a declaration mentions, for the dependency closure. -/
def FuncDef.idents (f : FuncDef) : List String :=
  (f.recv.map (·.2)).toList ++ f.params.flatMap (exprIdents ·.2) ++ f.results.flatMap exprIdents ++
    stmtIdents f.body

/-- The names a type declaration mentions. An interface mentions only the
signatures of the methods named in `mentioned`, the ones the code calls. -/
def typeIdents (mentioned : List String) (td : TypeDef) : List String :=
  match td.type with
  | .interfaceType _ methods =>
    methods.flatMap fun
      | f@(.mk _ [name] _ _) => if mentioned.contains name then fieldIdents f else []
      | f => fieldIdents f
  | ty => exprIdents ty

/-- The roots and every package-level declaration they reach. A method is
reached when its receiver type is reached and its name is mentioned. -/
def closure (pkg : Pkg) (roots : List String) : List String := Id.run do
  let known := pkg.types.map (·.name) ++ pkg.funcs.map (·.name) ++ pkg.values.map (·.name)
  let mut reached : List String := roots
  let mut fuel := 1000
  let mut changed := true
  while changed && fuel > 0 do
    fuel := fuel - 1
    changed := false
    let funcIdents := (pkg.funcs.filter (reached.contains ·.name)).flatMap FuncDef.idents
    let valueIdents := (pkg.values.filter (reached.contains ·.name)).flatMap fun v =>
      (v.type.map exprIdents).getD [] ++ (v.value.map exprIdents).getD []
    let mentioned := funcIdents ++ valueIdents
    let typeIds := (pkg.types.filter (reached.contains ·.name)).flatMap (typeIdents mentioned)
    let methods := pkg.funcs.filterMap fun f =>
      match f.recv with
      | some (_, t) =>
        if reached.contains t && mentioned.contains (f.name.drop (t.length + 1)).toString then
          some f.name
        else none
      | none => none
    for m in (mentioned ++ typeIds).filter known.contains ++ methods do
      if !reached.contains m then
        reached := reached ++ [m]
        changed := true
  return reached

/-! ## Type expressions -/

def lookupType (n : String) : TM (Option TypeDef) := do
  return (← get).pkg.types.find? (·.name == n)

partial def resolveType (e : Expr) : TM Ty := do
  let cfg := (← get).cfg
  match e with
  | .ident s n =>
    match n with
    | "int" | "int64" => return .int
    | "bool" => return .bool
    | "string" => return .string
    | "byte" | "uint8" => return .byte
    | "error" => return .error
    | _ =>
      if cfg.eraseTypes.contains n then return .erased
      match ← lookupType n with
      | some _ => return .named n
      | none => fail s s!"the type '{n}' is not supported"
  | .selector _ (.ident _ "context") "Context" => return .context
  | .star s inner =>
    match inner with
    | .ident _ n => if cfg.eraseTypes.contains n then return .erased else fail s "pointers are not supported"
    | _ => fail s "pointers are not supported"
  | .sliceType _ elem => return .slice (← resolveType elem)
  | .arrayType s (.lit _ .int raw) elem =>
    match raw.toNat? with
    | some n => return .array n (← resolveType elem)
    | none => fail s "an array length must be a decimal literal"
  | .paren _ inner => resolveType inner
  | other => fail other.span "this type is not supported"

/-- The Lean type for `t`. `State` is the state type of the current function, for
interface types. -/
partial def leanType (t : Ty) : TM String := do
  match t with
  | .int => return "Int"
  | .bool => return "Bool"
  | .string => return "String"
  | .byte => return "UInt8"
  | .error => return "Go.error"
  | .context => return "Go.Context"
  | .slice e => return s!"(List {← leanType e})"
  | .array n e => return s!"(Vector {← leanType e} {n})"
  | .tuple [] => return "Unit"
  | .tuple ts => return "(" ++ " × ".intercalate (← ts.mapM leanType) ++ ")"
  | .named n =>
    match ← lookupType n with
    | some { type := .interfaceType .., .. } => return s!"({leanName n} {(← get).stateVar})"
    | _ => return leanName n
  | .erased | .nil => return "Unit"

/-- The underlying type of a named type, through aliases and definitions. -/
partial def underlying (t : Ty) : TM Ty := do
  match t with
  | .named n =>
    match ← lookupType n with
    | some { type := .structType .., .. } | some { type := .interfaceType .., .. } => return t
    | some td => underlying (← resolveType td.type)
    | none => return t
  | _ => return t

partial def zeroOf (t : Ty) : TM String := do
  match ← underlying t with
  | .int => return "0"
  | .bool => return "false"
  | .string => return "\"\""
  | .byte => return "0"
  | .error => return "(none : Go.error)"
  | .slice _ => return "[]"
  | .array n e => return s!"(Vector.replicate {n} {← zeroOf e})"
  | .named n => return "({} : " ++ leanName n ++ ")"
  | _ => return "default"

/-- The fields of a struct type, by name. -/
def structFields (n : String) : TM (List (String × Ty)) := do
  match ← lookupType n with
  | some { type := .structType _ fields, .. } =>
    (fieldNames fields).mapM fun (fname, ty) => do return (fname, ← resolveType ty)
  | _ => return []

/-- An interface's methods: parameter types and result types. -/
def ifaceMethod (iface method : String) : TM (Option (List Ty × List Ty)) := do
  match ← lookupType iface with
  | some { type := .interfaceType _ ms, .. } =>
    for m in ms do
      match m with
      | .mk _ [name] (.funcType _ ps rs) _ =>
        if name == method then
          let params ← (fieldNames ps).mapM fun (_, t) => resolveType t
          let results ← ((rs.getD []).flatMap fun
              | .mk _ [] t _ => [t]
              | .mk _ ns t _ => ns.map fun _ => t).mapM resolveType
          return some (params, results)
      | _ => pure ()
    return none
  | _ => return none

def isIface (t : Ty) : TM Bool := do
  match t with
  | .named n =>
    match ← lookupType n with
    | some { type := .interfaceType .., .. } => return true
    | _ => return false
  | _ => return false

def resultTy : List Ty → Ty
  | [t] => t
  | ts => .tuple ts

/-! ## Scopes -/

def lookupLocal (n : String) : TM (Option Local) := do
  for scope in (← get).scopes do
    if let some l := scope.find? (·.go == n) then return some l
  return none

def freshName (base : String) : TM String := do
  let s ← get
  let mut name := leanName base
  let mut k := 1
  while s.used.contains name do
    k := k + 1
    name := leanName s!"{base}_{k}"
  modify fun s => { s with used := name :: s.used }
  return name

def declare (go : String) (ty : Ty) : TM Local := do
  let lean ← if go == "_" then pure "_" else freshName go
  let l : Local := { go, lean, ty }
  modify fun s => match s.scopes with
    | top :: rest => { s with scopes := (l :: top) :: rest }
    | [] => { s with scopes := [[l]] }
  return l

def pushScope : TM Unit := modify fun s => { s with scopes := [] :: s.scopes }
def popScope : TM Unit := modify fun s => { s with scopes := s.scopes.tail! }

def inCurrentScope (n : String) : TM (Option Local) := do
  return ((← get).scopes.head?.bind (·.find? (·.go == n)))

/-! ## Expressions -/

def stripUnderscores (s : String) : String := s.foldl (fun acc c => if c == '_' then acc else acc.push c) ""

def intLiteral (span : Span) (raw : String) : TM String := do
  let raw := stripUnderscores raw
  -- Go reads `017` as octal.
  if raw.length > 1 && raw.startsWith "0" && (raw.toList.all Char.isDigit) then
    let v := raw.toList.drop 1 |>.foldl (fun acc c => acc * 8 + (c.toNat - '0'.toNat)) 0
    return toString v
  if raw.startsWith "0x" || raw.startsWith "0X" || raw.startsWith "0b" || raw.startsWith "0B" ||
      raw.startsWith "0o" || raw.startsWith "0O" || raw.toList.all Char.isDigit then
    return raw.toLower
  fail span s!"the literal {raw} is not supported"

/-- The value of a Go string literal, raw or interpreted. -/
def stringValue (span : Span) (raw : String) : TM String := do
  let cs := raw.toList
  -- Not String.ofList, which raises bad_alloc in the WebAssembly build (wasm/).
  if cs.head? == some '`' then return (cs.drop 1 |>.dropLast).foldl String.push ""
  let body := (cs.drop 1).dropLast
  let rec go : List Char → String → Except String String
    | [], acc => .ok acc
    | '\\' :: c :: rest, acc =>
      match c with
      | 'n' => go rest (acc.push '\n')
      | 't' => go rest (acc.push '\t')
      | 'r' => go rest (acc.push '\r')
      | '\\' => go rest (acc.push '\\')
      | '"' => go rest (acc.push '"')
      | '\'' => go rest (acc.push '\'')
      | _ => .error s!"the escape \\{c} is not supported"
    | c :: rest, acc => go rest (acc.push c)
  match go body "" with
  | .ok v => return v
  | .error m => fail span m

def arithOps : List String := ["+", "-", "*"]
def compareOps : List String := ["==", "!=", "<", "<=", ">", ">="]

mutual

/-- A pure expression, and its type. Calls with effects are refused here;
statements bind them first. -/
partial def transExpr (e : Expr) : TM (String × Ty) := do
  match e with
  | .ident s n =>
    match n with
    | "true" => return ("true", .bool)
    | "false" => return ("false", .bool)
    | "nil" => return ("none", .nil)
    | _ =>
      if let some l ← lookupLocal n then
        if l.ty == .erased then fail s s!"'{n}' is erased and cannot be used here"
        return (l.lean, l.ty)
      let pkg := (← get).pkg
      if let some v := pkg.values.find? (·.name == n) then
        let ty ← match v.type with
          | some t => resolveType t
          | none => match v.value with
            | some (.call _ (.selector _ (.ident _ "errors") "New") _ _) => pure .error
            | some val => do let (_, t) ← transExpr val; pure t
            | none => fail s s!"'{n}' has no type"
        return (leanName n, ty)
      fail s s!"unknown name '{n}'"
  | .lit s .int raw => return (← intLiteral s raw, .int)
  | .lit s .string raw => return ((← stringValue s raw).quote, .string)
  | .lit s _ _ => fail s "this literal is not supported"
  | .paren _ inner =>
    let (x, t) ← transExpr inner
    return (s!"({x})", t)
  | .selector s obj name =>
    let (x, t) ← transExpr obj
    match ← underlying t with
    | .named tn =>
      let fields ← structFields tn
      match fields.find? (·.1 == name) with
      | some (_, ft) => return (s!"{x}.{leanName name}", ft)
      | none => fail s s!"'{tn}' has no field '{name}'"
    | _ => fail s s!"cannot read the field '{name}' here"
  | .unary s op arg =>
    let (x, t) ← transExpr arg
    match op with
    | "!" => return (s!"(!{x})", .bool)
    | "-" => return (s!"(Go.wrap64 (-{x}))", t)
    | _ => fail s s!"the operator '{op}' is not supported"
  | .binary s op lhs rhs =>
    let (a, ta) ← transExpr lhs
    let (b, tb) ← transExpr rhs
    if op == "&&" || op == "||" then return (s!"({a} {op} {b})", .bool)
    if op == "!=" && tb == .nil then return (s!"({a}).isSome", .bool)
    if op == "==" && tb == .nil then return (s!"({a}).isNone", .bool)
    if op == "==" || op == "!=" then return (s!"({a} {op} {b})", .bool)
    if compareOps.contains op then return (s!"(decide ({a} {op} {b}))", .bool)
    let t := if ta == .int then ta else tb
    if arithOps.contains op then
      match ← underlying t with
      | .int => return (s!"(Go.wrap64 ({a} {op} {b}))", t)
      | .string => if op == "+" then return (s!"({a} ++ {b})", t) else fail s "not supported"
      | _ => fail s s!"the operator '{op}' is not supported on this type"
    fail s s!"the operator '{op}' is not supported"
  | .composite s (some ty) elts => transComposite s ty elts
  | .call s callee args _ => transPureCall s callee args
  | other => fail other.span "this expression is not supported"

/-- An expression where a value of type `expected` stands, so that `nil` gets
the right zero value: `none` for an error, `[]` for a slice. -/
partial def transExprAs (e : Expr) (expected : Ty) : TM String := do
  match e with
  | .ident _ "nil" => zeroOf expected
  | _ => return (← transExpr e).1

partial def transComposite (s : Span) (tyExpr : Expr) (elts : List Expr) : TM (String × Ty) := do
  let ty ← resolveType tyExpr
  match ← underlying ty with
  | .array .. =>
    if !elts.isEmpty then fail s "array literals with elements are not supported"
    return (s!"({← zeroOf ty} : {← leanType ty})", ty)
  | .slice elem =>
    let items ← elts.mapM fun e => do return (← transExpr e).1
    return (s!"([{", ".intercalate items}] : List {← leanType elem})", ty)
  | .named tn =>
    let fields ← structFields tn
    let mut parts := #[]
    for elt in elts do
      match elt with
      | .keyValue _ (.ident _ fname) v =>
        match fields.find? (·.1 == fname) with
        | some (_, fty) => parts := parts.push s!"{leanName fname} := {← transExprAs v fty}"
        | none => fail s s!"'{tn}' has no field '{fname}'"
      | other => fail other.span "struct literals must name their fields"
    return (s!"(\{ {", ".intercalate parts.toList} } : {leanName tn})", ty)
  | _ => fail s "this composite literal is not supported"

partial def transPureCall (s : Span) (callee : Expr) (args : List Expr) : TM (String × Ty) := do
  match callee with
  | .ident _ "len" =>
    let (x, _) ← transExpr args.head!
    return (s!"(Int.ofNat ({x}).length)", .int)
  | .ident _ "append" =>
    let (xs, t) ← transExpr args.head!
    let items ← args.tail.mapM fun a => do return (← transExpr a).1
    return (s!"({xs} ++ [{", ".intercalate items}])", t)
  | .ident _ "make" =>
    let ty ← resolveType args.head!
    match args[1]? with
    | some (Expr.lit _ LitKind.int "0") => return (s!"([] : {← leanType ty})", ty)
    | _ => fail s "only make([]T, 0, …) is supported"
  | .selector _ (.ident _ "fmt") "Errorf" =>
    match args with
    | .lit fs .string raw :: inner :: _ =>
      if (← stringValue fs raw).startsWith "%w" then
        let (x, _) ← transExpr inner
        return (s!"(Go.errorf {x})", .error)
      fail s "only fmt.Errorf with a leading %w is supported"
    | _ => fail s "only fmt.Errorf with a leading %w is supported"
  | .selector _ (.ident _ "errors") "New" =>
    match args with
    | [.lit ls .string raw] => return (s!"(some (.sentinel {(← stringValue ls raw).quote}))", .error)
    | _ => fail s "errors.New takes a string literal"
  | .ident _ name =>
    let pkg := (← get).pkg
    if let some td := pkg.types.find? (·.name == name) then
      -- A conversion to a named type with the same Lean type.
      let (x, _) ← transExpr args.head!
      let _ := td
      return (s!"({x} : {leanName name})", .named name)
    if (← get).effectful.contains name then fail s s!"'{name}' has effects; call it in its own statement"
    match pkg.funcs.find? (·.name == name) with
    | some f =>
      let argStrs ← transArgs f args
      let results ← f.results.mapM resolveType
      return (s!"({leanName name}{argStrs})", resultTy results)
    | none => fail s s!"unknown function '{name}'"
  | .selector _ obj method =>
    let (x, t) ← transExpr obj
    match ← underlying t with
    | .named tn =>
      match (← get).pkg.funcs.find? (·.name == s!"{tn}.{method}") with
      | some f =>
        let argStrs ← transArgs f args
        let results ← f.results.mapM resolveType
        return (s!"({x}.{leanName method}{argStrs})", resultTy results)
      | none => fail s s!"unknown method '{method}'"
    | _ => fail s "this call is not supported"
  | _ => fail s "this call is not supported"

/-- The arguments of a call to `f`, without those of erased types. -/
partial def transArgs (f : FuncDef) (args : List Expr) : TM String := do
  let mut out := ""
  for ((_, pty), a) in f.params.zip args do
    if (← resolveType pty) == .erased then continue
    out := out ++ " " ++ (← transExpr a).1
  return out

end

/-! ## Effects and erasure -/

/-- A call with effects: a method on an interface value, or a function with
effects. Returns the Lean action and its result types. -/
def transEffectCall? (e : Expr) : TM (Option (String × List Ty)) := do
  match e with
  | .call s (.selector _ (.ident _ obj) method) args _ =>
    match ← lookupLocal obj with
    | some l =>
      if ← isIface l.ty then
        let .named iface := l.ty | return none
        match ← ifaceMethod iface method with
        | some (_, results) =>
          modify fun st => if st.methods.contains (iface, method) then st
            else { st with methods := st.methods ++ [(iface, method)] }
          let argStrs ← args.mapM fun a => do return (← transExpr a).1
          return some (s!"{l.lean}.{leanName method} {" ".intercalate argStrs}", results)
        | none => fail s s!"'{iface}' has no method '{method}'"
      return none
    | none => return none
  | .call _ (.ident _ name) args _ =>
    if !(← get).effectful.contains name then return none
    let some f := (← get).pkg.funcs.find? (·.name == name) | return none
    let mut argStrs := #[]
    for ((_, pty), a) in f.params.zip args do
      if (← resolveType pty) == .erased then continue
      argStrs := argStrs.push (← transExpr a).1
    let results ← f.results.mapM resolveType
    return some (s!"{leanName name} {" ".intercalate argStrs.toList}", results)
  | _ => return none

def erasedPackageCall (e : Expr) : TM Bool := do
  let pkgs := (← get).cfg.erasePackages
  return (exprIdents e).any pkgs.contains

/-- The names in an expression, except bare names passed as call arguments:
an argument of an erased type is dropped from the call, not erased with it. -/
partial def usedIdents : Expr → List String
  | .call _ f args _ =>
    usedIdents f ++ args.flatMap fun
      | .ident .. => []
      | a => usedIdents a
  | .binary _ _ a b => usedIdents a ++ usedIdents b
  | .unary _ _ a | .paren _ a => usedIdents a
  | e => exprIdents e

/-- The names in a statement's own expressions. For a compound statement,
these are its header, not the statements inside it, which are erased or kept
one by one. -/
partial def ownIdents (st : Stmt) : List String :=
  match st with
  | .block .. => []
  | .ifStmt _ init cond _ _ => ((init.map ownIdents).getD []) ++ usedIdents cond
  | .range _ _ k v x _ => ((k.map exprIdents).getD []) ++ ((v.map exprIdents).getD []) ++ exprIdents x
  | .forStmt _ init cond post _ =>
    ((init.map stmtIdents).getD []) ++ ((cond.map exprIdents).getD []) ++ ((post.map stmtIdents).getD [])
  | .switchStmt _ init tag _ _ => ((init.map stmtIdents).getD []) ++ ((tag.map exprIdents).getD [])
  | .assign _ _ lhs rhs => lhs.flatMap exprIdents ++ rhs.flatMap usedIdents
  | .expr _ e => usedIdents e
  | .ret _ es => es.flatMap usedIdents
  | _ => stmtIdents st

/-- The statement reads an erased value or calls an erased package. -/
def mentionsErased (st : Stmt) : TM Bool := do
  let names := ownIdents st
  let pkgs := (← get).cfg.erasePackages
  if names.any pkgs.contains then return true
  for n in names do
    if let some l ← lookupLocal n then
      if l.ty == .erased then return true
  return false

/-- The root variable of an assignment target. -/
def targetRoot : Expr → Option String
  | .ident _ n => some n
  | .selector _ e _ | .index _ e _ | .paren _ e | .star _ e => targetRoot e
  | _ => none

/-- An erased statement may only assign through erased values or define new
erased locals, so that dropping it changes nothing else. -/
partial def checkErasable (st : Stmt) : TM Unit := do
  let isErasedName (n : String) : TM Bool := do
    match ← lookupLocal n with
    | some l => return l.ty == .erased
    | none => return false
  match st with
  | .assign s ":=" lhs rhs =>
    for r in rhs do
      if !(← erasedPackageCall r) then fail s "this statement cannot be erased"
    for l in lhs do
      match l with
      | .ident _ n => discard (declare n .erased)
      | _ => fail s "this statement cannot be erased"
  | .assign s _ lhs _ =>
    for t in lhs do
      match targetRoot t with
      | some n => if !(← isErasedName n) then fail s "this statement cannot be erased"
      | none => fail s "this statement cannot be erased"
  | .incDec s _ t =>
    match targetRoot t with
    | some n => if !(← isErasedName n) then fail s "this statement cannot be erased"
    | none => fail s "this statement cannot be erased"
  | .ifStmt s none (.binary _ "!=" (.ident _ n) (.ident _ "nil")) body none =>
    if !(← isErasedName n) then fail s "this statement cannot be erased"
    checkErasable body
  | .block _ ss => for x in ss do checkErasable x
  | other => fail other.span "this statement cannot be erased"

/-! ## Statements -/

def indent (n : Nat) (line : String) : String := "".pushn ' ' (2 * n) ++ line

/-- Locals declared outside `body` that it assigns with `=`, `op=` or `++`. -/
partial def assignedNames : Stmt → List String
  | .assign _ op lhs _ =>
    if op == ":=" then [] else lhs.filterMap targetRoot
  | .incDec _ _ t => (targetRoot t).toList
  | .block _ ss => ss.flatMap assignedNames
  | .ifStmt _ i _ b e =>
    ((i.map assignedNames).getD []) ++ assignedNames b ++ ((e.map assignedNames).getD [])
  | .forStmt _ i _ p b =>
    ((i.map assignedNames).getD []) ++ ((p.map assignedNames).getD []) ++ assignedNames b
  | .range _ _ _ _ _ b => assignedNames b
  | .switchStmt _ i _ _ cs =>
    ((i.map assignedNames).getD []) ++ cs.flatMap fun (.mk _ _ body) => body.flatMap assignedNames
  | _ => []

/-- The last statement always leaves the block. -/
def endsBlock : List Stmt → Bool
  | [] => false
  | ss => match ss.getLast! with
    | .ret .. | .brk _ | .cont _ => true
    | _ => false

def tupleOf : List String → String
  | [] => "()"
  | [x] => x
  | xs => "(" ++ ", ".intercalate xs ++ ")"

def bindMut (name : String) : TM String := do
  return if (← get).mutNames.contains name then "let mut " else "let "

mutual

partial def transStmts (mode : Mode) (depth : Nat) (ss : List Stmt) : TM (List String) := do
  let mut out := []
  for st in ss do
    out := out ++ (← transStmt mode depth st)
  return out

partial def transBlock (mode : Mode) (depth : Nat) (body : Stmt) : TM (List String) := do
  pushScope
  let lines ← match body with
    | .block _ ss => transStmts mode depth ss
    | other => transStmt mode depth other
  popScope
  return if lines.isEmpty then [indent depth "pure ()"] else lines

partial def transReturn (mode : Mode) (depth : Nat) (s : Span) (results : List Expr) :
    TM (List String) := do
  let expected := (← get).results
  if results.length != expected.length then fail s "the number of results does not match"
  let vals ← (results.zip expected).mapM fun (r, t) => transExprAs r t
  let v := tupleOf vals
  match mode with
  | .top => return [indent depth s!"return {v}"]
  | .loop .. => return [indent depth s!"return .inr {v}"]

partial def transStmt (mode : Mode) (depth : Nat) (st : Stmt) : TM (List String) := do
  if ← mentionsErased st then
    checkErasable st
    return []
  match st with
  | .block _ _ => transBlock mode depth st
  | .expr s e =>
    match ← transEffectCall? e with
    | some (action, _) => return [indent depth s!"let _ ← {action}"]
    | none => fail s "only calls with effects can stand alone"
  | .ret s results =>
    -- `return f(…)` where `f` has effects.
    if let [r] := results then
      if let some (action, _) ← transEffectCall? r then
        let t ← freshName "result"
        let ret := match mode with
          | .top => s!"return {t}"
          | .loop .. => s!"return .inr {t}"
        return [indent depth s!"let {t} ← {action}", indent depth ret]
    transReturn mode depth s results
  | .brk s =>
    match mode with
    | .loop _ _ _ written => return [indent depth s!"return .inl {tupleOf (written.map (·.lean))}"]
    | .top => fail s "'break' outside a loop"
  | .cont s =>
    match mode with
    | .loop name fixed next written =>
      let args := " ".intercalate (fixed ++ [next] ++ written.map (·.lean))
      return [indent depth s!"return (← {name} {args})"]
    | .top => fail s "'continue' outside a loop"
  | .assign s op lhs rhs => transAssign depth s op lhs rhs
  | .incDec s op target =>
    match target with
    | .ident _ n =>
      let some l ← lookupLocal n | fail s s!"unknown name '{n}'"
      let sym := if op == "++" then "+" else "-"
      return [indent depth s!"{l.lean} := Go.wrap64 ({l.lean} {sym} 1)"]
    | _ => fail s "only a local can be incremented"
  | .decl s (.mk _ "var" specs) =>
    let mut out := []
    for spec in specs do
      match spec with
      | .value _ names (some ty) [] =>
        let t ← resolveType ty
        for n in names do
          let l ← declare n t
          out := out ++ [indent depth s!"{← bindMut n}{l.lean} : {← leanType t} := {← zeroOf t}"]
      | _ => fail s "only 'var x T' is supported here"
    return out
  | .ifStmt _ init cond body els =>
    pushScope
    let initLines ← match init with
      | some i => transStmt mode depth i
      | none => pure []
    let (c, _) ← transExpr cond
    let thenLines ← transBlock mode (depth + 1) body
    let elseLines ← match els with
      | some e => do
        let ls ← transBlock mode (depth + 1) e
        pure ([indent depth "else"] ++ ls)
      | none => pure []
    popScope
    return initLines ++ [indent depth s!"if {c} then"] ++ thenLines ++ elseLines
  | .switchStmt s init (some tag) _ clauses =>
    pushScope
    let initLines ← match init with
      | some i => transStmt mode depth i
      | none => pure []
    let (t, _) ← transExpr tag
    let tagName ← freshName "tag"
    let mut lines := initLines ++ [indent depth s!"let {tagName} := {t}"]
    let cases := clauses.filter fun (.mk _ es _) => es.isSome
    let dflt := clauses.find? fun (.mk _ es _) => es.isNone
    let mut d := depth
    for (.mk _ es body) in cases do
      for b in body do
        if b matches .brk _ then fail s "'break' in a switch is not supported"
      let conds ← (es.getD []).mapM fun e => do return s!"{tagName} == {(← transExpr e).1}"
      lines := lines ++ [indent d s!"if {" || ".intercalate conds} then"]
      pushScope
      let bodyLines ← transStmts mode (d + 1) body
      popScope
      lines := lines ++ (if bodyLines.isEmpty then [indent (d + 1) "pure ()"] else bodyLines)
      lines := lines ++ [indent d "else"]
      d := d + 1
    match dflt with
    | some (.mk _ _ body) =>
      pushScope
      let bodyLines ← transStmts mode d body
      popScope
      lines := lines ++ (if bodyLines.isEmpty then [indent d "pure ()"] else bodyLines)
    | none => lines := lines ++ [indent d "pure ()"]
    popScope
    return lines
  | .range s op key value iterable body => transRange mode depth s op key value iterable body
  | other => fail other.span "this statement is not supported"

partial def transAssign (depth : Nat) (s : Span) (op : String) (lhs rhs : List Expr) :
    TM (List String) := do
  -- `a, b := f(…)` or `a, b = f(…)` where `f` has effects.
  if let [r] := rhs then
    if let some (action, results) ← transEffectCall? r then
      if results.length != lhs.length then fail s "the number of values does not match"
      let mut binders := #[]
      let mut after := #[]
      for (l, t) in lhs.zip results do
        match l with
        | .ident _ "_" => binders := binders.push "_"
        | .ident _ n =>
          let existing ← if op == ":=" then inCurrentScope n else lookupLocal n
          match existing with
          | some loc =>
            let tmp ← freshName n
            binders := binders.push tmp
            after := after.push (indent depth s!"{loc.lean} := {tmp}")
          | none =>
            let loc ← declare n t
            if (← get).mutNames.contains n then
              let tmp ← freshName n
              binders := binders.push tmp
              after := after.push (indent depth s!"let mut {loc.lean} := {tmp}")
            else binders := binders.push loc.lean
        | other => fail other.span "only locals can be assigned here"
      return [indent depth s!"let {tupleOf binders.toList} ← {action}"] ++ after.toList
  match op with
  | ":=" | "=" =>
    if lhs.length != rhs.length then fail s "the number of values does not match"
    let vals ← rhs.mapM transExpr
    let mut lines := []
    for (l, (v, t)) in lhs.zip vals do
      match l with
      | .ident _ "_" => pure ()
      | .ident _ n =>
        let existing ← if op == ":=" then inCurrentScope n else lookupLocal n
        match existing with
        | some loc => lines := lines ++ [indent depth s!"{loc.lean} := {v}"]
        | none =>
          if op == "=" then fail s s!"unknown name '{n}'"
          let ty := if t == .nil then .error else t
          let loc ← declare n ty
          lines := lines ++ [indent depth s!"{← bindMut n}{loc.lean} := {v}"]
      | other => fail other.span "only locals can be assigned"
    return lines
  | _ =>
    let sym := (op.dropEnd 1).toString
    match lhs, rhs with
    | [.ident _ n], [r] =>
      let some loc ← lookupLocal n | fail s s!"unknown name '{n}'"
      let (v, _) ← transExpr r
      if arithOps.contains sym then
        return [indent depth s!"{loc.lean} := Go.wrap64 ({loc.lean} {sym} {v})"]
      fail s s!"the operator '{op}' is not supported"
    | _, _ => fail s s!"'{op}' takes one local"

partial def transRange (mode : Mode) (depth : Nat) (s : Span) (op : Option String)
    (key value : Option Expr) (iterable : Expr) (body : Stmt) : TM (List String) := do
  if op == some "=" then fail s "range with '=' is not supported"
  let (xs, xsTy) ← transExpr iterable
  let elemTy ← match ← underlying xsTy with
    | .slice e => pure e
    | _ => fail iterable.span "only a range over a slice is supported"
  let st ← get
  let loopName := s!"{st.fnName}.loop{st.loopCount + 1}"
  modify fun st => { st with loopCount := st.loopCount + 1 }
  -- The visible locals the body mentions, and those it assigns.
  let mentioned := stmtIdents body
  let assigned := assignedNames body
  let visible := st.scopes.flatten
  let mut seen : List String := []
  let mut fixed : Array Local := #[]
  let mut written : Array Local := #[]
  for l in visible do
    if seen.contains l.go || l.ty == .erased then continue
    seen := l.go :: seen
    if assigned.contains l.go then written := written.push l
    else if mentioned.contains l.go then fixed := fixed.push l
  let monad := if st.inEffectful then s!"StateM {st.stateVar}" else "Id"
  let writtenTy ← if written.size == 1 then leanType written[0]!.ty
    else leanType (.tuple (written.toList.map (·.ty)))
  let resTy ← leanType (resultTy st.results)
  -- The loop function.
  let savedScopes := st.scopes
  let savedUsed := st.used
  -- Erased locals stay known as erased, so that statements reading them are
  -- erased inside the loop too.
  let erasedLocals := visible.filter (·.ty == .erased)
  modify fun st => { st with scopes := [fixed.toList ++ written.toList ++ erasedLocals] }
  modify fun st => { st with used := (fixed.toList ++ written.toList).map (·.lean) }
  let idx ← match key with
    | some (.ident _ k) => if k == "_" then freshName "i" else (declare k .int) >>= fun l => pure l.lean
    | _ => freshName "i"
  let elem ← match value with
    | some (.ident _ v) => if v == "_" then freshName "x" else (declare v elemTy) >>= fun l => pure l.lean
    | _ => freshName "x"
  let restName ← freshName "rest"
  let fixedNames := fixed.toList.map (·.lean)
  let next := s!"({idx} + 1) {restName}"
  let loopMode := Mode.loop loopName fixedNames next written.toList
  let bodyStmts := match body with
    | .block _ ss => ss
    | other => [other]
  let bodyLines ← transStmts loopMode 2 bodyStmts
  let tail := if endsBlock bodyStmts then []
    else [indent 2 s!"{loopName} {" ".intercalate (fixedNames ++ [next] ++ written.toList.map (·.lean))}"]
  let sigmaBinder := if st.inEffectful then s!"\{{st.stateVar} : Type} " else ""
  let fixedParams ← fixed.toList.mapM fun l => do return s!"({l.lean} : {← leanType l.ty})"
  let header := s!"def {loopName} {sigmaBinder}{" ".intercalate fixedParams} :\n    Int → List {← leanType elemTy} → " ++
    String.join (← written.toList.mapM fun l => do return s!"{← leanType l.ty} → ") ++
    s!"{monad} (Sum {if written.isEmpty then "Unit" else writtenTy} {resTy})"
  let ws := written.toList.map (·.lean)
  let nilCase := if ws.isEmpty then indent 1 s!"| _, [] => pure (.inl ())" else
    indent 1 s!"| _, [], {", ".intercalate ws} => pure (.inl {tupleOf ws})"
  let consHead := indent 1 s!"| {idx}, {elem} :: {restName}{String.join (ws.map (", " ++ ·))} => do"
  let rebinds := ws.map fun w => indent 2 s!"let mut {w} := {w}"
  let defText := "\n".intercalate ([header, nilCase, consHead] ++ rebinds ++ bodyLines ++ tail)
  modify fun st => { st with aux := st.aux.push defText, scopes := savedScopes, used := savedUsed ++ st.used }
  -- The call, and the locals it changed.
  let resultName ← freshName "loop"
  let args := " ".intercalate (fixedNames ++ ["0", xs] ++ ws)
  let mut lines := [indent depth s!"match (← {loopName} {args}) with",
    indent depth s!"| .inr {resultName} => " ++ (match mode with
      | .top => s!"return {resultName}"
      | .loop .. => s!"return .inr {resultName}")]
  let fresh ← ws.mapM fun w => freshName w
  lines := lines ++ [indent depth s!"| .inl {tupleOf fresh} =>"]
  for (w, f) in ws.zip fresh do
    lines := lines ++ [indent (depth + 1) s!"{w} := {f}"]
  if ws.isEmpty then lines := lines ++ [indent (depth + 1) "pure ()"]
  return lines

end

/-! ## Declarations -/

def transType (td : TypeDef) : TM String := do
  modify fun s => { s with file := td.file }
  match td.type with
  | .structType _ fields =>
    let mut lines := [s!"structure {leanName td.name} where"]
    for (fname, ty) in fieldNames fields do
      let t ← resolveType ty
      lines := lines ++ [s!"  {leanName fname} : {← leanType t} := {← zeroOf t}"]
    return "\n".intercalate lines ++ "\nderiving Inhabited"
  | .interfaceType .. =>
    let used := (← get).methods.filter (·.1 == td.name)
    let stateVar := (← get).stateVar
    let mut lines := [s!"structure {leanName td.name} ({stateVar} : Type) where"]
    for (_, m) in used do
      let some (params, results) ← ifaceMethod td.name m | fail td.type.span s!"no method {m}"
      let ps ← params.mapM leanType
      let r ← leanType (resultTy results)
      lines := lines ++ [s!"  {leanName m} : {String.join (ps.map (· ++ " → "))}StateM {stateVar} {r}"]
    return "\n".intercalate lines
  | other =>
    let t ← resolveType other
    return s!"abbrev {leanName td.name} := {← leanType t}"

def transValue (v : ValueDef) : TM String := do
  modify fun s => { s with file := v.file }
  let some value := v.value | fail v.span "a package-level value needs an initializer"
  let (x, t) ← transExpr value
  let t ← match v.type with
    | some te => resolveType te
    | none => pure t
  return s!"def {leanName v.name} : {← leanType t} := {x}"

def transFunc (f : FuncDef) : TM String := do
  let isEff := (← get).effectful.contains f.name
  let assigned := assignedNames f.body
  modify fun s => { s with file := f.file, scopes := [[]], used := [] }
  modify fun s => { s with fnName := leanName f.name, loopCount := 0 }
  modify fun s => { s with inEffectful := isEff, mutNames := assigned }
  let results ← f.results.mapM resolveType
  modify fun s => { s with results }
  let mut params := #[]
  if let some (r, t) := f.recv then
    let l ← declare r (.named t)
    params := params.push s!"({l.lean} : {leanName t})"
  for (n, ty) in f.params do
    let t ← resolveType ty
    if t == .erased then
      discard (declare n .erased)
      continue
    let l ← declare n t
    params := params.push s!"({l.lean} : {← leanType t})"
  let resTy ← leanType (resultTy results)
  let stateVar := (← get).stateVar
  let monad := if isEff then s!"StateM {stateVar} {resTy}" else resTy
  let sigma := if isEff then s!"\{{stateVar} : Type} " else ""
  let body := match f.body with
    | .block _ ss => ss
    | other => [other]
  -- Parameters that the body assigns need `let mut`.
  let rebinds := (← get).scopes.head!.reverse.filterMap fun l =>
    if assigned.contains l.go && l.ty != .erased then
      some (indent 1 s!"let mut {l.lean} := {l.lean}")
    else none
  let lines ← transStmts .top 1 body
  let open_ := if isEff then "do" else "Id.run do"
  let name := match f.recv with
    | some (_, t) => s!"{leanName t}.{leanName (f.name.drop (t.length + 1)).toString}"
    | none => leanName f.name
  let aux := (← get).aux
  modify fun s => { s with aux := #[] }
  let defText := s!"def {name} {sigma}{" ".intercalate params.toList} : {monad} := {open_}\n" ++
    "\n".intercalate (rebinds ++ lines)
  return "\n\n".intercalate (aux.toList ++ [defText])

/-- Functions with effects: those that call a method on an interface
parameter, and those that call a function with effects. -/
def findEffectful (pkg : Pkg) (names : List String) : List String := Id.run do
  let funcs := pkg.funcs.filter fun f => names.contains f.name
  let ifaceTypes := pkg.types.filterMap fun t =>
    match t.type with
    | .interfaceType .. => some t.name
    | _ => none
  let mut eff := funcs.filterMap fun f =>
    if f.params.any (fun (_, ty) => match ty with
        | .ident _ n => ifaceTypes.contains n
        | _ => false) then some f.name else none
  let mut changed := true
  while changed do
    changed := false
    for f in funcs do
      if !eff.contains f.name && (stmtIdents f.body).any eff.contains then
        eff := eff ++ [f.name]
        changed := true
  return eff

/-- Order declarations so that each comes after those it mentions. -/
def topoOrder (names : List String) (deps : String → List String) : List String := Id.run do
  let mut done : List String := []
  let mut fuel := names.length * names.length + 10
  while done.length < names.length && fuel > 0 do
    fuel := fuel - 1
    for n in names do
      if !done.contains n && (deps n).all fun d => d == n || done.contains d || !names.contains d then
        done := done ++ [n]
  return done ++ names.filter (!done.contains ·)

def translatePkg (pkg : Pkg) (cfg : Config) (ns : String) (sources : List String)
    (idents : List String := []) : Except String String := do
  let reached := closure pkg cfg.roots
  for r in cfg.roots do
    if !(pkg.funcs.any (·.name == r)) then throw s!"no function '{r}' in the package"
  let types := pkg.types.filter fun t => reached.contains t.name && !cfg.eraseTypes.contains t.name
  let values := pkg.values.filter fun v => reached.contains v.name
  let funcs := pkg.funcs.filter fun f => reached.contains f.name
  let effectful := findEffectful pkg reached
  let deps (n : String) : List String :=
    (pkg.funcs.filter (·.name == n)).flatMap FuncDef.idents ++
      (pkg.types.filter (·.name == n)).flatMap (exprIdents ·.type) ++
      (pkg.values.filter (·.name == n)).flatMap fun v => (v.value.map exprIdents).getD []
  let typeOrder := topoOrder (types.map (·.name)) deps
  let funcOrder := topoOrder (funcs.map (·.name)) fun n =>
    deps n ++ (match n.splitOn "." with
      | [_, m] => funcs.filter (fun f => (f.name.splitOn ".").getLast? == some m) |>.map (·.name)
      | _ => [])
  let run : TM String := do
    -- Functions first, so the interface methods they call are known.
    let mut funcTexts := #[]
    for n in funcOrder do
      let some f := funcs.find? (·.name == n) | continue
      funcTexts := funcTexts.push (← transFunc f)
    let mut typeTexts := #[]
    for n in typeOrder do
      let some td := types.find? (·.name == n) | continue
      typeTexts := typeTexts.push (← transType td)
    let mut valueTexts := #[]
    for v in values do
      valueTexts := valueTexts.push (← transValue v)
    let header := s!"-- Generated by tolean from {", ".intercalate sources}. Do not edit.\n" ++
      "import tolean.Go.Spec.Basic\n\nset_option linter.unusedVariables false\n\n" ++
      s!"namespace {ns}\n\nopen tolean\n\n"
    return header ++ "\n\n".intercalate (typeTexts.toList ++ valueTexts.toList ++ funcTexts.toList) ++
      s!"\n\nend {ns}\n"
  let stateVar := ("State" :: (List.range 1000).map (s!"State{· + 1}")).find? (!idents.contains ·)
  match run.run { pkg, cfg, effectful, stateVar := stateVar.getD "State" } with
  | .ok (text, _) => return text
  | .error e => throw e

/-- Translate the Go files `files` (path and source) of one package. -/
def translate (files : List (String × String)) (cfg : Config) (ns : String) : Except String String := do
  let parsed ← files.mapM fun (path, src) =>
    match parse src with
    | .ok f => .ok (path, f)
    | .error e => .error (e.render path)
  let pkg ← readPkg parsed
  -- Every identifier in the package, so the state type parameter avoids them.
  let idents := files.flatMap fun (_, src) => match lex src with
    | .ok tokens => tokens.toList.filterMap fun (t : Token) => match t.kind with
      | .ident name => some name
      | _ => none
    | .error _ => []
  translatePkg pkg cfg ns (files.map (·.1)) idents

/-- The exported top-level functions of a package: the default roots. -/
def exportedFunctions (files : List (String × String)) : Except String (List String) := do
  let parsed ← files.mapM fun (path, src) =>
    match parse src with
    | .ok f => .ok (path, f)
    | .error e => .error (e.render path)
  let pkg ← readPkg parsed
  return pkg.funcs.filterMap fun f =>
    if !f.name.contains '.' && (f.name.front.isUpper) then some f.name else none

end tolean.Go.Translate
