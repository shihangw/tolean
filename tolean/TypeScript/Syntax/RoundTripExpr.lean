import tolean.TypeScript.Syntax.RoundTrip

/-!
The parser's round trip for expressions, on tokens: the parser reads the
tokens that `Syntax/Source.lean` prints for an expression as the same
expression, apart from spans.

The expression parser has one function for each level of precedence, and
`Expr.wfAt T level e` states that the function for `level` reads `e` when the
target edition is `T`. Each level stops before a token that cannot continue
it, and `Ends` states which tokens those are. In a few places the parser also
looks at the tokens after a node, and `Expr.afterOK` states what it checks
there. The tokens of a word such as `>=` touch, and inside an expression a
line break comes only between `async` and the `(` of a call of it.
`Touching` states both.
`exprs_read` proves the round trip by induction on the parser's fuel.

The statement parser calls `parseExpression` and `parseAssign` with the fuel
that `budget` gives, and `parseExpression_budget` and `parseAssign_budget`
state the round trip for that fuel. The brackets of an expression's tokens
match, and the tokens have no `;`, so what `afterOK` checks before a `;` does
not depend on the tokens after it (`afterOK_semicolon`).
-/
namespace tolean.TypeScript.Syntax

open tolean

/-- `closesTypeArguments` on token kinds. -/
def closesKinds (depth : Nat) : List TokenKind → Bool
  | [] => false
  | k :: rest =>
    match k with
    | .eof => false
    | .punct "(" | .punct "[" | .punct "{" => closesKinds (depth + 1) rest
    | .punct ")" | .punct "]" | .punct "}" => if depth == 0 then false else closesKinds (depth - 1) rest
    | .punct ";" => if depth == 0 then false else closesKinds depth rest
    | .punct ">" => true
    | _ => closesKinds depth rest

theorem closesTypeArguments_kinds (depth : Nat) (ts : List Token) :
    Parse.closesTypeArguments depth ts = closesKinds depth (ts.map (·.kind)) := by
  induction ts generalizing depth with
  | nil => rfl
  | cons t ts ih =>
    simp only [Parse.closesTypeArguments, closesKinds, List.map_cons]
    split <;> simp_all

/-- The tokens of a word touch. A `lineBreak` has no tokens, and no tokens
touch trivially. -/
theorem Placed.chained {w : Word} {ws : List Word} {a b : List Token} (ha : a.map (·.kind) = w)
    (h : Placed w ws a b) : Chained a := by
  match w, h with
  | [], _ => simp at ha; subst ha; trivial
  | _ :: _, h => exact h.1

/-- No line break comes before the token after a word with tokens, when a word
with tokens follows it. -/
theorem Placed.next {w v : Word} {ws : List Word} {a : List Token} {y : Token} {b : List Token}
    (hw : w ≠ []) (hv : v ≠ []) (h : Placed w (v :: ws) a (y :: b)) : y.newlineBefore = false := by
  match w, hw, h with
  | _ :: _, _, h => exact h.2 v rfl hv y rfl

/-- After a `lineBreak`, the next token starts a new line. -/
theorem Touching.after_lineBreak {ts : List Token} {ws : List Word} (h : Touching ts (lineBreak :: ws)) :
    (∀ y ∈ ts.head?, y.newlineBefore = true) ∧ Touching ts ws := by
  obtain ⟨a, b, rfl, ha, hp, hb⟩ := h
  simp [lineBreak] at ha; subst ha
  exact ⟨hp, hb⟩

/-- The `callBreak` of a call has no tokens. -/
@[simp] theorem flatten_callBreak (e : Expr) : (callBreak e).flatten = [] := by
  unfold callBreak; split <;> rfl

/-- After the callee `async`, the `(` of a call starts a new line. -/
theorem Touching.after_callBreak {ts : List Token} {o : Expr} {ws : List Word} (h : Touching ts (callBreak o ++ ws)) :
    (∀ sp, o = .ident sp "async" → ∀ y ∈ ts.head?, y.newlineBefore = true) ∧ Touching ts ws := by
  cases o with
  | ident sp name =>
    by_cases hn : name = "async"
    · subst hn
      have h' : Touching ts (lineBreak :: ws) := by simpa [callBreak] using h
      exact ⟨fun _ _ => (Touching.after_lineBreak h').1, (Touching.after_lineBreak h').2⟩
    · exact ⟨fun _ ho => (by cases ho; exact absurd rfl hn), by simpa [callBreak, hn] using h⟩
  | _ => exact ⟨fun _ ho => (by cases ho), by simpa [callBreak] using h⟩

/-- The levels of the expression parser, one for each of its functions. -/
inductive Level where
  | assign
  | cond
  /-- `parseBinary` with this least precedence. -/
  | bin (minPrec : Nat)
  | unary
  | postfix
  | lhs
  | primary

/-- The levels in order: each reads the ones after it. -/
@[simp] def Level.rank : Level → Nat
  | .assign => 6 | .cond => 5 | .bin _ => 4 | .unary => 3 | .postfix => 2 | .lhs => 1 | .primary => 0

/-- The least precedence of the right operand of `op`: `**` is
right-associative, and the others are left-associative. -/
def rhsPrec (op : BinOp) : Nat := if op == .exp then op.precedence else op.precedence + 1

/-- What the left operand `l` of `op` must be, besides an expression that
`parseBinary` reads: a binary operand binds at least as tightly as `op`, and
the left operand of `**` is neither binary nor unary, as in `(-a) ** b`. -/
def leftOK (op : BinOp) : Expr → Bool
  | .binary _ op' _ _ => op != .exp && decide (op.precedence ≤ op'.precedence)
  | .unary .. => op != .exp
  | _ => true

/-- What the operand `l` of `as const` or `satisfies T` must be: a binary
operand binds at least as tightly as `<`, whose precedence they have, and
the operand is no name that the parser refuses there. -/
def leftOKType : Expr → Bool
  | .binary _ op' _ _ => decide (BinOp.lt.precedence ≤ op'.precedence)
  | e => !Parse.refusedBeforeType e

/-- `e` ends in `as const` or `satisfies T`: it is one, or it is a binary node
whose right operand ends in one. -/
def Expr.endsInType : Expr → Bool
  | .asConst .. | .satisfies .. => true
  | .binary _ _ _ r => r.endsInType
  | _ => false

/-- An operator whose symbol starts with one of `Parse.typeEnders`, so that it
may not follow `as const` or `satisfies T`. -/
def BinOp.followsType : BinOp → Bool
  | .lt | .shl | .bitOr | .bitAnd => false
  | _ => true

/-- The token after `as const` or `satisfies T` is none of `Parse.typeEnders`. -/
def TypeOK (rest : List Token) : Prop :=
  ∀ u ∈ rest.head?, ∀ p, u.kind = .punct p → p ∉ Parse.typeEnders

/-- A name that an expression reads, or that a shorthand property binds. -/
def exprName (n : String) : Bool := !Parse.refusedNames.contains n

/-- The target edition has `op`. -/
def BinOp.allowedIn (T : Edition) (op : BinOp) : Bool :=
  (op != .exp || T.supports .exponent) && (op != .coalesce || T.supports .nullishCoalescing)

def AssignOp.allowedIn (T : Edition) : AssignOp → Bool
  | .exp => T.supports .exponent
  | .and | .or | .coalesce => T.supports .logicalAssignment
  | _ => true

/-- The kinds of the tokens of `e`. -/
def Expr.tokens (e : Expr) : List TokenKind := e.words.flatten

def Property.tokens (p : Property) : List TokenKind := p.words.flatten

/-- The first of `after` is not `k`. -/
def notFirst (k : TokenKind) (after : List TokenKind) : Bool := after.head? != some k

def Param.wf (p : Param) : Bool := exprName p.name && (match p.type with | some t => t.wf | none => true)

/-- One parameter without a type, which an arrow function may have without
parentheses. -/
def bareParam : List Param → Bool
  | [⟨_, _, _, none⟩] => true
  | _ => false

theorem arrowParams_cases (parens : Bool) (ps : List Param) :
    (∃ p, parens = false ∧ ps = [p] ∧ arrowParams parens ps = [identWord p.name]) ∨
      arrowParams parens ps = enclose "(" ")" (ps.map Param.words) := by
  match parens, ps with
  | false, [p] => exact .inl ⟨p, rfl, rfl, rfl⟩
  | false, [] => exact .inr rfl
  | false, _ :: _ :: _ => exact .inr rfl
  | true, _ => exact .inr rfl

mutual

/-- `e` is an expression that the parser's function for `level` reads, when the
target edition is `T`, apart from what follows it. -/
def Expr.wfAt (T : Edition) : Level → Expr → Bool
  | .assign, .assign _ op target value =>
    target.wfAt T .cond && target.isSimpleTarget && op.allowedIn T && value.wfAt T .assign
  | .assign, .arrow _ parens params body =>
    (parens || bareParam params) && params.all (fun p => p.wf && !p.optional) && body.wfAt T .assign &&
      notFirst (.punct "{") body.tokens
  | .assign, e => e.wfAt T .cond
  | .cond, .cond _ test a b =>
    test.wfAt T (.bin 0) && a.wfAt T .assign && b.wfAt T .assign && !test.endsInType
  | .cond, e => e.wfAt T (.bin 0)
  | .bin m, .binary _ op l r =>
    decide (m ≤ op.precedence) && op.allowedIn T && l.wfAt T (.bin m) && r.wfAt T (.bin (rhsPrec op)) &&
      leftOK op l &&
      (if op == .coalesce then !l.isLogical && !r.isLogical
       else if op == .and || op == .or then !l.isCoalesce && !r.isCoalesce else true) &&
      (!l.endsInType || op.followsType)
  | .bin m, .asConst _ e =>
    decide (m ≤ BinOp.lt.precedence) && e.wfAt T (.bin m) && leftOKType e
  | .bin m, .satisfies _ e t =>
    decide (m ≤ BinOp.lt.precedence) && e.wfAt T (.bin m) && leftOKType e && t.wf
  | .bin _, e => e.wfAt T .unary
  | .unary, .unary _ _ arg => arg.wfAt T .unary
  | .unary, .prefix _ _ arg => arg.wfAt T .lhs && arg.isSimpleTarget
  | .unary, e => e.wfAt T .postfix
  | .postfix, .postfix _ _ arg => arg.wfAt T .lhs && arg.isSimpleTarget
  | .postfix, e => e.wfAt T .lhs
  | .lhs, .member _ obj _ => obj.wfAt T .lhs
  | .lhs, .optMember _ obj _ => T.supports .optionalChaining && obj.wfAt T .lhs
  | .lhs, .index _ obj idx => obj.wfAt T .lhs && idx.wfAt T .assign
  | .lhs, .call _ callee args => callee.wfAt T .lhs && Expr.allWF T args
  | .lhs, e => e.wfAt T .primary
  | .primary, .ident _ name => exprName name
  | .primary, .number .. | .primary, .bigint .. | .primary, .string .. | .primary, .bool ..
  | .primary, .null _ => true
  | .primary, .paren _ inner => inner.wfAt T .assign
  | .primary, .array _ elems => Expr.allWF T elems
  | .primary, .object _ props => Property.allWF T props
  | .primary, .new _ callee typeArgs args =>
    typeName callee && TypeExpr.allWF typeArgs && Expr.allWF T args
  | .primary, _ => false
termination_by level e => (sizeOf e, level.rank)

/-- `e` is an element of an array literal, or an argument, that
`parseElement` reads: `...v` or `v`, where `parseAssign` reads `v`. -/
def Expr.elemWF (T : Edition) : Expr → Bool
  | .spread _ v => v.wfAt T .assign
  | e => e.wfAt T .assign
termination_by e => (sizeOf e, 7)

def Expr.allWF (T : Edition) : List Expr → Bool
  | [] => true
  | e :: es => e.elemWF T && Expr.allWF T es
termination_by es => (sizeOf es, 8)

def Property.wf (T : Edition) : Property → Bool
  | .shorthand _ name => exprName name
  | .keyValue _ _ value => value.wfAt T .assign
  | .spread _ value => T.supports .objectSpread && value.wfAt T .assign
termination_by p => (sizeOf p, 7)

def Property.allWF (T : Edition) : List Property → Bool
  | [] => true
  | p :: ps => p.wf T && Property.allWF T ps
termination_by ps => (sizeOf ps, 7)

end

mutual

/-- What the parser checks in the tokens after a node, when `after` follows
`e`: no `>` closes what tsc could read as type arguments after a `<` or `<<`
operator, and no `{` follows `(…)`. The parser also checks what follows a
call of `async`, but only when no line break comes before its `(`, and the
printer puts one there. -/
def Expr.afterOK (after : List TokenKind) : Expr → Bool
  | .binary _ op l r =>
    (if op == .lt || op == .shl then !closesKinds 0 (r.tokens ++ after) else true) &&
      l.afterOK ((symbol op.symbol) ++ r.tokens ++ after) && r.afterOK after
  | .paren _ inner => notFirst (.punct "{") after && inner.afterOK (.punct ")" :: after)
  | .member _ obj name => obj.afterOK (.punct "." :: propertyName name ++ after)
  | .optMember _ obj name => obj.afterOK (.punct "?." :: propertyName name ++ after)
  | .index _ obj idx =>
    obj.afterOK (.punct "[" :: idx.tokens ++ .punct "]" :: after) && idx.afterOK (.punct "]" :: after)
  | .call _ callee args =>
    callee.afterOK ((enclose "(" ")" (Expr.wordsOf args)).flatten ++ after) &&
      Expr.afterOKList (.punct ")" :: after) args
  | .unary _ _ arg | .prefix _ _ arg => arg.afterOK after
  | .postfix _ op arg => arg.afterOK (.punct op.symbol :: after)
  | .cond _ test a b =>
    test.afterOK (.punct "?" :: a.tokens ++ .punct ":" :: b.tokens ++ after) &&
      a.afterOK (.punct ":" :: b.tokens ++ after) && b.afterOK after
  | .assign _ op target value => target.afterOK (symbol op.symbol ++ value.tokens ++ after) &&
      value.afterOK after
  | .arrow _ _ _ body => body.afterOK after
  | .asConst _ e => e.afterOK (.ident "as" :: .keyword "const" :: after)
  | .satisfies _ e t => e.afterOK (.ident "satisfies" :: t.tokens ++ after)
  | .array _ elems => Expr.afterOKList (.punct "]" :: after) elems
  | .object _ props => Property.afterOKList (.punct "}" :: after) props
  | .new _ _ _ args => Expr.afterOKList (.punct ")" :: after) args
  | .spread _ e => e.afterOK after
  | .ident .. | .number .. | .bigint .. | .string .. | .bool .. | .null _ => true

/-- `afterOK` for each of `items`, with a `,` between two of them, which
`close` follows. -/
def Expr.afterOKList (close : List TokenKind) : List Expr → Bool
  | [] => true
  | [e] => e.afterOK close
  | e :: rest => e.afterOK (.punct "," :: joined "," (rest.map Expr.tokens) ++ close) &&
      Expr.afterOKList close rest

def Property.afterOK (after : List TokenKind) : Property → Bool
  | .shorthand .. => true
  | .keyValue _ _ value | .spread _ value => value.afterOK after

def Property.afterOKList (close : List TokenKind) : List Property → Bool
  | [] => true
  | [p] => p.afterOK close
  | p :: rest => p.afterOK (.punct "," :: joined "," (rest.map Property.tokens) ++ close) &&
      Property.afterOKList close rest

end

/-! ### Reading an expression -/

/-- `p` reads the tokens of `x`, laid out as the printer writes them and
followed by any rest that `ends` allows and that `afterOK` accepts, as `x`
apart from spans, and leaves the rest. The target edition is `T`. After its
first token, a line break comes only where the printer puts one, as
`Touching` states, but one may come before the first, as at the start of a
statement. -/
def ReadsW {α : Type} (T : Edition) (erase : α → α) (words : α → List Word)
    (afterOK : List TokenKind → α → Bool) (p : ParseM α) (x : α) (ends : List Token → Prop) : Prop :=
  ∀ (s : ParseState) (ts rest : List Token), s.target = T → s.rest = ts ++ rest →
    s.left = s.rest.length → Touching ts (words x) → (∀ y ∈ ts.tail, NoBreak y) → rest ≠ [] →
    ends rest → afterOK (rest.map (·.kind)) x = true →
    ∃ x' s', p s = .ok x' s' ∧ erase x' = erase x ∧ Leaves s s' rest

/-- `ReadsW` for an expression. -/
abbrev ReadsE (T : Edition) (p : ParseM Expr) (e : Expr) (ends : List Token → Prop) : Prop :=
  ReadsW T Expr.erase Expr.words (fun after e => e.afterOK after) p e ends

/-- A token after the first of `a ++ b`, when `a` has tokens. -/
theorem tail_sub {ts a b : List Token} (h : ts = a ++ b) (ha : a ≠ []) {y : Token}
    (hy : y ∈ a.tail ∨ y ∈ b) : y ∈ ts.tail := by
  subst h
  cases a with
  | nil => exact absurd rfl ha
  | cons x a => simpa using hy

/-- `ReadsW` for a property of an object literal. -/
abbrev ReadsP (T : Edition) (p : ParseM Property) (q : Property) (ends : List Token → Prop) : Prop :=
  ReadsW T Property.erase Property.words (fun after q => q.afterOK after) p q ends

/-- The expression that `parsePrimary` gives for a token that is not a name, a
`(`, a `[` or a `{`, when it reads one. -/
def simpleExpr (x : Token) : Option Expr :=
  match x.kind with
  | .number text => some (.number x.span text)
  | .bigint text => some (.bigint x.span text)
  | .string value => some (.string x.span value)
  | .keyword "true" => some (.bool x.span true)
  | .keyword "false" => some (.bool x.span false)
  | .keyword "null" => some (.null x.span)
  | _ => none

theorem parsePrimary_simple (f : Nat) (s : ParseState) (x u : Token) (r : List Token) (e : Expr)
    (hs : s.rest = x :: u :: r) (he : simpleExpr x = some e) :
    Parse.parsePrimary (f + 1) s = .ok e (past s x (u :: r)) := by
  unfold simpleExpr at he
  split at he <;> simp only [Option.some.injEq, reduceCtorEq] at he <;> subst he <;>
    simp_all [Parse.parsePrimary, Parse.peek_eq hs, Parse.advance_eq hs, discard, Functor.mapConst,
      EStateM.map, bind, EStateM.bind, pure, EStateM.pure]

theorem parsePrimary_ident (f : Nat) (s : ParseState) (x u : Token) (r : List Token) (name : String)
    (hs : s.rest = x :: u :: r) (hx : x.kind = .ident name) (hn : name ∉ Parse.refusedNames) :
    Parse.parsePrimary (f + 1) s = .ok (.ident x.span name) (past s x (u :: r)) := by
  simp [Parse.parsePrimary, Parse.peek_eq hs, hx, Parse.readName, Parse.advance_eq hs, hn,
    bind, EStateM.bind, pure, EStateM.pure]

/-! ### Where each level stops -/

/-- The next token does not continue a left-hand side: no member, index or
call, and nothing that the parser refuses there. -/
def EndsLhs (rest : List Token) : Prop :=
  ∀ u ∈ rest.head?, u.kind ≠ .punct "." ∧ u.kind ≠ .punct "[" ∧ u.kind ≠ .punct "(" ∧
    u.kind ≠ .punct "?." ∧ (u.kind = .punct "!" → u.newlineBefore = true)

/-- Nor a `++` or `--` on the same line. -/
def EndsPostfix (rest : List Token) : Prop :=
  EndsLhs rest ∧ ∀ u ∈ rest.head?, (u.kind = .punct "++" ∨ u.kind = .punct "--") → u.newlineBefore = true

/-- No `as` or `satisfies` on the same line comes next, unless `m` is above the
precedence of `<`, which they have. -/
def NoTypeOp (m : Nat) (rest : List Token) : Prop :=
  ∀ u ∈ rest.head?, Parse.isTypeOperator u = true → BinOp.lt.precedence < m

/-- A token that is not a name is not `as` or `satisfies`. -/
theorem noTypeOp_of {m : Nat} {x : Token} {r : List Token} (hx : ∀ n, x.kind ≠ .ident n) :
    NoTypeOp m (x :: r) := by
  intro u hu h
  simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hu
  subst hu
  simp only [Parse.isTypeOperator, Token.isIdent, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
  rcases h.1 with h' | h' <;> exact absurd h' (hx _)

/-- Nor a binary operator of precedence `m` or more. -/
def EndsBin (m : Nat) (rest : List Token) : Prop :=
  EndsPostfix rest ∧ (∀ s, s.rest = rest →
    ∃ o, Parse.peekBinaryOp s = .ok o s ∧ ∀ op w, o = some (op, w) → op.precedence < m) ∧
    NoTypeOp m rest

/-- Nor a `?`. -/
def EndsCond (rest : List Token) : Prop :=
  EndsBin 0 rest ∧ ∀ u ∈ rest.head?, u.kind ≠ .punct "?"

/-- Nor an arrow or an assignment. -/
def EndsAssign (rest : List Token) : Prop :=
  EndsCond rest ∧ (∀ u ∈ rest.head?, u.kind ≠ .punct "=>") ∧
    ∀ s, s.rest = rest → Parse.peekAssignOp s = .ok none s

/-- Nor a `,`, the comma operator that `parseExpression` refuses. -/
def EndsExpr (rest : List Token) : Prop :=
  EndsAssign rest ∧ ∀ u ∈ rest.head?, u.kind ≠ .punct ","

/-- The punctuators that close or separate, and end every expression. -/
def separators : List String := [")", "]", "}", ";", ",", ":"]

theorem peekBinaryOp_separator {s : ParseState} {u : Token} {r : List Token} {p : String}
    (hs : s.rest = u :: r) (hu : u.kind = .punct p) (hp : p ∈ separators) :
    Parse.peekBinaryOp s = .ok none s := by
  simp [separators] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [Parse.peekBinaryOp, Parse.peek_eq hs, hu, BinOp.ofSymbol?, BinOp.all, BinOp.symbol, bind,
      EStateM.bind, pure, EStateM.pure]

theorem peekAssignOp_separator {s : ParseState} {u : Token} {r : List Token} {p : String}
    (hs : s.rest = u :: r) (hu : u.kind = .punct p) (hp : p ∈ separators) :
    Parse.peekAssignOp s = .ok none s := by
  simp [separators] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [Parse.peekAssignOp, Parse.peek_eq hs, hu, AssignOp.ofSymbol?, AssignOp.all, AssignOp.symbol,
      bind, EStateM.bind, pure, EStateM.pure]

/-- A separator ends an expression at every level but `parseExpression`'s. -/
theorem endsAssign_separator {u : Token} {r : List Token} {p : String} (hu : u.kind = .punct p)
    (hp : p ∈ separators) : EndsAssign (u :: r) := by
  have hne : ∀ q, q ∉ separators → u.kind ≠ .punct q := fun q hq h => by
    rw [hu] at h; injection h with h; subst h; exact hq hp
  refine ⟨⟨⟨⟨fun t ht => ?_, fun t ht => ?_⟩, fun s hs => ⟨none, peekBinaryOp_separator hs hu hp, by simp⟩,
    noTypeOp_of (by simp [hu])⟩, fun t ht => ?_⟩, fun t ht => ?_, fun s hs => peekAssignOp_separator hs hu hp⟩ <;>
    simp at ht <;> subst ht
  · refine ⟨hne "." (by decide), hne "[" (by decide), hne "(" (by decide), hne "?." (by decide),
      fun h => absurd h (hne "!" (by decide))⟩
  · rintro (h | h)
    · exact absurd h (hne "++" (by decide))
    · exact absurd h (hne "--" (by decide))
  · exact hne "?" (by decide)
  · exact hne "=>" (by decide)

/-! ### Touching tokens -/

theorem Touching.append_split : ∀ {ts : List Token} {ws₁ ws₂ : List Word}, Touching ts (ws₁ ++ ws₂) →
    ∃ a b, ts = a ++ b ∧ Touching a ws₁ ∧ Touching b ws₂
  | ts, [], ws₂, h => ⟨[], ts, rfl, rfl, h⟩
  | ts, w :: ws₁, ws₂, h => by
    obtain ⟨a, b, rfl, ha, hc, hb⟩ := h
    obtain ⟨b₁, b₂, rfl, h₁, h₂⟩ := Touching.append_split hb
    refine ⟨a ++ b₁, b₂, by simp, ⟨a, b₁, rfl, ha, ?_, h₁⟩, h₂⟩
    match w, hc with
    | [], hc =>
      intro y hy
      cases b₁ with
      | nil => simp at hy
      | cons z _ => exact hc y (by simpa using hy)
    | _ :: _, hc =>
      refine ⟨hc.1, fun v hv hne y hy => ?_⟩
      cases ws₁ with
      | nil => simp at hv
      | cons v' _ =>
        cases b₁ with
        | nil => simp at hy
        | cons z _ => exact hc.2 v (by simpa using hv) hne y (by simpa using hy)

/-- A word of one token is one token of that kind. -/
theorem Touching.cons_one {ts : List Token} {k : TokenKind} {ws : List Word} (h : Touching ts ([k] :: ws)) :
    ∃ x ts', ts = x :: ts' ∧ x.kind = k ∧ Touching ts' ws := by
  obtain ⟨a, b, rfl, ha, _, hb⟩ := h
  match a, ha with
  | [x], ha => exact ⟨x, b, rfl, by simpa using ha, hb⟩

/-! ### The first token of an expression -/

/-- A token that can start an expression. -/
def startsExpr : TokenKind → Bool
  | .ident _ | .number _ | .bigint _ | .string _ | .keyword _ => true
  | .punct p => p ∈ ["(", "[", "{", "!", "-", "+", "~", "++", "--", "..."]
  | .eof => false

/-- An expression has tokens, and the first can start an expression. -/
theorem Expr.first : ∀ e : Expr, ∃ k, e.tokens.head? = some k ∧ startsExpr k = true
  | .ident _ n => ⟨.ident n, by simp [Expr.tokens, Expr.words, identWord], rfl⟩
  | .number _ t => ⟨.number t, by simp [Expr.tokens, Expr.words], rfl⟩
  | .bigint _ t => ⟨.bigint t, by simp [Expr.tokens, Expr.words], rfl⟩
  | .string _ v => ⟨.string v, by simp [Expr.tokens, Expr.words], rfl⟩
  | .bool _ b => ⟨.keyword (if b then "true" else "false"), by simp [Expr.tokens, Expr.words, keywordWord], rfl⟩
  | .null _ => ⟨.keyword "null", by simp [Expr.tokens, Expr.words, keywordWord], rfl⟩
  | .array _ es => ⟨.punct "[", by simp [Expr.tokens, Expr.words, enclose, punctWord], by decide⟩
  | .object _ ps => ⟨.punct "{", by simp [Expr.tokens, Expr.words, enclose, punctWord], by decide⟩
  | .paren _ i => ⟨.punct "(", by simp [Expr.tokens, Expr.words, punctWord], by decide⟩
  | .new .. => ⟨.keyword "new", by simp [Expr.tokens, Expr.words, keywordWord], rfl⟩
  | .spread .. => ⟨.punct "...", by simp [Expr.tokens, Expr.words, punctWord], by decide⟩
  | .arrow _ parens ps _ => by
    rcases arrowParams_cases parens ps with ⟨p, _, _, h⟩ | h
    · exact ⟨.ident p.name, by simp [Expr.tokens, Expr.words, h, identWord], rfl⟩
    · exact ⟨.punct "(", by simp [Expr.tokens, Expr.words, h, enclose, punctWord], by decide⟩
  | .member _ o _ => by
    obtain ⟨k, h, hk⟩ := Expr.first o
    exact ⟨k, by simp [Expr.tokens, Expr.words] at h ⊢; simp [h], hk⟩
  | .optMember _ o _ => by
    obtain ⟨k, h, hk⟩ := Expr.first o
    exact ⟨k, by simp [Expr.tokens, Expr.words] at h ⊢; simp [h], hk⟩
  | .index _ o _ => by
    obtain ⟨k, h, hk⟩ := Expr.first o
    exact ⟨k, by simp [Expr.tokens, Expr.words] at h ⊢; simp [h], hk⟩
  | .call _ c _ => by
    obtain ⟨k, h, hk⟩ := Expr.first c
    exact ⟨k, by simp [Expr.tokens, Expr.words] at h ⊢; simp [h], hk⟩
  | .postfix _ _ a => by
    obtain ⟨k, h, hk⟩ := Expr.first a
    exact ⟨k, by simp [Expr.tokens, Expr.words] at h ⊢; simp [h], hk⟩
  | .binary _ _ l _ => by
    obtain ⟨k, h, hk⟩ := Expr.first l
    exact ⟨k, by simp [Expr.tokens, Expr.words] at h ⊢; simp [h], hk⟩
  | .asConst _ l => by
    obtain ⟨k, h, hk⟩ := Expr.first l
    exact ⟨k, by simp [Expr.tokens, Expr.words] at h ⊢; simp [h], hk⟩
  | .satisfies _ l _ => by
    obtain ⟨k, h, hk⟩ := Expr.first l
    exact ⟨k, by simp [Expr.tokens, Expr.words] at h ⊢; simp [h], hk⟩
  | .cond _ t _ _ => by
    obtain ⟨k, h, hk⟩ := Expr.first t
    exact ⟨k, by simp [Expr.tokens, Expr.words] at h ⊢; simp [h], hk⟩
  | .assign _ _ t _ => by
    obtain ⟨k, h, hk⟩ := Expr.first t
    exact ⟨k, by simp [Expr.tokens, Expr.words] at h ⊢; simp [h], hk⟩
  | .unary _ op _ => by
    have key : ∃ k, symbol op.symbol = [k] ∧ startsExpr k = true := by
      cases op
      · exact ⟨.punct "!", by simp [symbol, UnaryOp.symbol, Lex.reservedWords, punctWord], by decide⟩
      · exact ⟨.punct "-", by simp [symbol, UnaryOp.symbol, Lex.reservedWords, punctWord], by decide⟩
      · exact ⟨.punct "+", by simp [symbol, UnaryOp.symbol, Lex.reservedWords, punctWord], by decide⟩
      · exact ⟨.punct "~", by simp [symbol, UnaryOp.symbol, Lex.reservedWords, punctWord], by decide⟩
      · exact ⟨.keyword "typeof", by simp [symbol, UnaryOp.symbol, Lex.reservedWords, keywordWord], by decide⟩
      · exact ⟨.keyword "void", by simp [symbol, UnaryOp.symbol, Lex.reservedWords, keywordWord], by decide⟩
    obtain ⟨k, hk, hs⟩ := key
    exact ⟨k, by simp [Expr.tokens, Expr.words, hk], hs⟩
  | .prefix _ op _ => by
    cases op
    · exact ⟨.punct "++", by simp [Expr.tokens, Expr.words, UpdateOp.symbol, punctWord], by decide⟩
    · exact ⟨.punct "--", by simp [Expr.tokens, Expr.words, UpdateOp.symbol, punctWord], by decide⟩

/-! ### Operators -/

/-- The derived `==` on positions is equality, so that a proof can read
`peekGreater`'s test that two tokens touch. -/
instance : ReflBEq Pos where
  rfl {a} := by cases a; simp [BEq.beq, instBEqPos.beq]

instance : LawfulBEq Pos where
  eq_of_beq {a b} h := by cases a; cases b; simp [BEq.beq, instBEqPos.beq] at h; simp [h]

theorem startsExpr_ne {k : TokenKind} (h : startsExpr k = true) : k ≠ .punct ">" ∧ k ≠ .punct "=" := by
  constructor <;> (intro e; subst e; simp [startsExpr] at h)

/-- Split the tokens `ha` of an operator's symbol, and read `hc` and `hs` for them. In a hygienic
macro, the pattern `rfl` is a name, so the steps name each equation and `subst` it. -/
macro "op_tokens " ha:ident hc:ident hs:ident : tactic => `(tactic|
  ((first
      | (obtain ⟨_, hx, _⟩ := $ha; subst hx)
      | ((repeat (replace $ha := List.map_eq_cons_iff.mp $ha; obtain ⟨_, _, hx, _, $ha:ident⟩ := $ha; subst hx));
          have hnil := List.map_eq_nil_iff.mp $ha; subst hnil))
    <;> (try simp [Chained] at $hc:ident) <;> simp at $hs:ident))

theorem peekBinaryOp_op {s : ParseState} {op : BinOp} {a : List Token} {u : Token} {r : List Token}
    (hs : s.rest = a ++ u :: r) (ha : a.map (·.kind) = symbol op.symbol) (hc : Chained a)
    (hu : startsExpr u.kind = true) :
    Parse.peekBinaryOp s = .ok (some (op, a.length)) s := by
  have ⟨h1, h2⟩ := startsExpr_ne hu
  cases op <;> simp [BinOp.symbol, symbol, Lex.reservedWords, punctWord, keywordWord] at ha <;> op_tokens ha hc hs <;>
    simp [Parse.peekBinaryOp, Parse.peek, Parse.peekGreater, Parse.peekAt_rest, *, Token.isPunct,
      BinOp.ofSymbol?, BinOp.all, BinOp.symbol, bind, EStateM.bind, pure, EStateM.pure]

theorem peekAssignOp_op {s : ParseState} {op : AssignOp} {a : List Token} {u : Token} {r : List Token}
    (hs : s.rest = a ++ u :: r) (ha : a.map (·.kind) = symbol op.symbol) (hc : Chained a)
    (hu : startsExpr u.kind = true) :
    Parse.peekAssignOp s = .ok (some (op, a.length)) s := by
  have ⟨h1, h2⟩ := startsExpr_ne hu
  cases op <;> simp [AssignOp.symbol, symbol, Lex.reservedWords, punctWord] at ha <;> op_tokens ha hc hs <;>
    simp [Parse.peekAssignOp, Parse.peek, Parse.peekGreater, Parse.peekAt_rest, *, Token.isPunct,
      AssignOp.ofSymbol?, AssignOp.all, AssignOp.symbol, bind, EStateM.bind, pure, EStateM.pure]

/-- No binary operator starts an assignment's symbol. -/
theorem peekBinaryOp_assignOp {s : ParseState} {op : AssignOp} {a : List Token} {u : Token} {r : List Token}
    (hs : s.rest = a ++ u :: r) (ha : a.map (·.kind) = symbol op.symbol) (hc : Chained a)
    (hu : startsExpr u.kind = true) :
    Parse.peekBinaryOp s = .ok none s := by
  have ⟨h1, h2⟩ := startsExpr_ne hu
  cases op <;> simp [AssignOp.symbol, symbol, Lex.reservedWords, punctWord] at ha <;> op_tokens ha hc hs <;>
    simp [Parse.peekBinaryOp, Parse.peek, Parse.peekGreater, Parse.peekAt_rest, *, Token.isPunct,
      BinOp.ofSymbol?, BinOp.all, BinOp.symbol, bind, EStateM.bind, pure, EStateM.pure]

theorem peekBinaryOp_question {s : ParseState} {x : Token} {r : List Token} (hs : s.rest = x :: r)
    (hx : x.kind = .punct "?") : Parse.peekBinaryOp s = .ok none s := by
  simp [Parse.peekBinaryOp, Parse.peek_eq hs, hx, BinOp.ofSymbol?, BinOp.all, BinOp.symbol, bind,
    EStateM.bind, pure, EStateM.pure]

/-- A token kind that continues no left-hand side and no postfix expression. -/
def stopsPostfix (k : TokenKind) : Bool :=
  k != .punct "." && k != .punct "[" && k != .punct "(" && k != .punct "?." && k != .punct "!" &&
    k != .punct "++" && k != .punct "--"

theorem endsPostfix_of {x : Token} {r : List Token} (h : stopsPostfix x.kind = true) : EndsPostfix (x :: r) := by
  simp only [stopsPostfix, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  refine ⟨fun t ht => ?_, fun t ht => ?_⟩ <;> simp at ht <;> subst ht
  · exact ⟨h1, h2, h3, h4, fun e => absurd e h5⟩
  · rintro (e | e)
    · exact absurd e h6
    · exact absurd e h7

theorem binOp_head (op : BinOp) : ∃ k ks, symbol op.symbol = k :: ks ∧ stopsPostfix k = true := by
  cases op <;> simp [BinOp.symbol, symbol, Lex.reservedWords, punctWord, keywordWord, stopsPostfix]

theorem assignOp_head (op : AssignOp) :
    ∃ k ks, symbol op.symbol = k :: ks ∧ stopsPostfix k = true ∧ k ≠ .punct "?" ∧ k ≠ .punct "=>" := by
  cases op <;> simp [AssignOp.symbol, symbol, Lex.reservedWords, punctWord, stopsPostfix]

theorem binOp_notIdent (op : BinOp) {k : TokenKind} {ks : List TokenKind} (h : symbol op.symbol = k :: ks)
    (n : String) : k ≠ .ident n := by
  cases op <;> simp [BinOp.symbol, symbol, Lex.reservedWords, punctWord, keywordWord] at h <;>
    (try obtain ⟨rfl, -⟩ := h) <;> (try rw [← h.1]) <;> simp

theorem assignOp_notIdent (op : AssignOp) {k : TokenKind} {ks : List TokenKind} (h : symbol op.symbol = k :: ks)
    (n : String) : k ≠ .ident n := by
  cases op <;> simp [AssignOp.symbol, symbol, Lex.reservedWords, punctWord] at h <;>
    (try obtain ⟨rfl, -⟩ := h) <;> (try rw [← h.1]) <;> simp

/-- A binary operator ends every level whose least precedence is above the
operator's. -/
theorem endsBin_binOp {op : BinOp} {m : Nat} {a : List Token} {u : Token} {r : List Token}
    (ha : a.map (·.kind) = symbol op.symbol) (hc : Chained a) (hu : startsExpr u.kind = true)
    (hm : op.precedence < m) : EndsBin m (a ++ u :: r) := by
  obtain ⟨k, ks, hk, hst⟩ := binOp_head op
  have hni := binOp_notIdent op hk
  rw [hk] at ha
  obtain ⟨x, a', rfl, hx, _⟩ := List.map_eq_cons_iff.mp ha
  refine ⟨endsPostfix_of (hx ▸ hst), fun s hs => ⟨_, peekBinaryOp_op (op := op) hs (ha.trans hk.symm) hc hu,
    fun op' w h => ?_⟩, noTypeOp_of (fun n => hx ▸ hni n)⟩
  simp at h; obtain ⟨rfl, _⟩ := h; exact hm

/-- An assignment's symbol ends a conditional expression. -/
theorem endsCond_assignOp {op : AssignOp} {a : List Token} {u : Token} {r : List Token}
    (ha : a.map (·.kind) = symbol op.symbol) (hc : Chained a) (hu : startsExpr u.kind = true) :
    EndsCond (a ++ u :: r) := by
  obtain ⟨k, ks, hk, hst, hq, _⟩ := assignOp_head op
  have hni := assignOp_notIdent op hk
  rw [hk] at ha
  obtain ⟨x, a', rfl, hx, _⟩ := List.map_eq_cons_iff.mp ha
  refine ⟨⟨endsPostfix_of (hx ▸ hst), fun s hs => ⟨_, peekBinaryOp_assignOp (op := op) hs (ha.trans hk.symm) hc hu,
    fun op' w h => by simp at h⟩, noTypeOp_of (fun n => hx ▸ hni n)⟩, fun t ht => ?_⟩
  simp at ht; subst ht; rw [hx]; exact hq

theorem endsBin_question {x : Token} {r : List Token} (hx : x.kind = .punct "?") : EndsBin 0 (x :: r) :=
  ⟨endsPostfix_of (by simp [hx, stopsPostfix]), fun s hs => ⟨_, peekBinaryOp_question hs hx, by simp⟩,
    noTypeOp_of (by simp [hx])⟩

theorem EndsBin.mono {m m' : Nat} {rest : List Token} (h : EndsBin m rest) (hm : m ≤ m') : EndsBin m' rest :=
  ⟨h.1, fun s hs => by
    obtain ⟨o, ho, hp⟩ := h.2.1 s hs
    exact ⟨o, ho, fun op w e => Nat.lt_of_lt_of_le (hp op w e) hm⟩,
    fun u hu ht => Nat.lt_of_lt_of_le (h.2.2 u hu ht) hm⟩

/-! ### Steps of the parser -/

theorem Parse.spanFrom_eq (start : Pos) (s : ParseState) :
    Parse.spanFrom start s = .ok ⟨start, s.lastStop⟩ s := by
  simp [Parse.spanFrom, get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind, pure, EStateM.pure]

theorem Parse.requireFeature_ok {t : Token} {f : Feature} {s : ParseState} (h : s.target.supports f = true) :
    Parse.requireFeature t f s = .ok () s := by
  simp [Parse.requireFeature, h, get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind, pure,
    EStateM.pure]

/-- `skip` reads the tokens `a`, which `b` follows. -/
theorem Parse.skip_ok : ∀ (a : List Token) {b : List Token} {s : ParseState}, s.rest = a ++ b → b ≠ [] →
    s.left = s.rest.length → ∃ s', Parse.skip a.length s = .ok () s' ∧ Leaves s s' b
  | [], b, s, hs, _, hl => ⟨s, by simp [Parse.skip, pure, EStateM.pure],
      Leaves.refl (by simpa using hs) (by simp [hl, hs])⟩
  | x :: a, b, s, hs, hb, hl => by
    have hs' : s.rest = x :: (a ++ b) := by simpa using hs
    have hne : a ++ b ≠ [] := by simp [hb]
    let s₁ : ParseState := { s with rest := a ++ b, left := s.left - 1, lastStop := x.span.stop }
    obtain ⟨s', h, hL⟩ := Parse.skip_ok a (s := s₁) rfl hb (by simp [s₁, hl, hs'])
    refine ⟨s', ?_, leaves_trans (leaves_advance hs' hl) hL⟩
    simp only [Parse.skip, discard, Functor.mapConst, Function.comp_apply, bind,
      EStateM.bind, EStateM.map, Parse.advance_cons hs' hne]
    exact h

theorem Parse.iterate_true {σ : Type} {step : σ → ParseM (σ × Bool)} {n : Nat} {acc acc' : σ}
    {s s' : ParseState} (h : step acc s = .ok (acc', true) s') :
    Parse.iterate (n + 1) acc step s = Parse.iterate n acc' step s' := by
  rw [Parse.iterate_succ]; simp [bind, EStateM.bind, h]

theorem Parse.iterate_false {σ : Type} {step : σ → ParseM (σ × Bool)} {n : Nat} {acc acc' : σ}
    {s s' : ParseState} (h : step acc s = .ok (acc', false) s') :
    Parse.iterate (n + 1) acc step s = .ok acc' s' := by
  rw [Parse.iterate_succ]; simp [bind, EStateM.bind, h, pure, EStateM.pure]

/-! ### Fuel -/

mutual

/-- How deep the subexpressions of `e` nest. -/
def Expr.height : Expr → Nat
  | .array _ es => Expr.heightOf es + 1
  | .object _ ps => Property.heightOf ps + 1
  | .paren _ i | .member _ i _ | .optMember _ i _ | .unary _ _ i | .prefix _ _ i | .postfix _ _ i =>
    i.height + 1
  | .index _ o i | .binary _ _ o i | .assign _ _ o i => max o.height i.height + 1
  | .call _ c as => max c.height (Expr.heightOf as) + 1
  | .new _ _ _ as => Expr.heightOf as + 1
  | .cond _ t a b => max t.height (max a.height b.height) + 1
  | .arrow _ _ _ b | .asConst _ b | .satisfies _ b _ => b.height + 1
  -- `parseElement` reads the value of a spread with the fuel it gets.
  | .spread _ e => e.height
  | .ident .. | .number .. | .bigint .. | .string .. | .bool .. | .null _ => 0

def Expr.heightOf : List Expr → Nat
  | [] => 0
  | e :: es => max e.height (Expr.heightOf es)

def Property.height : Property → Nat
  | .shorthand .. => 0
  | .keyValue _ _ v | .spread _ v => v.height

def Property.heightOf : List Property → Nat
  | [] => 0
  | p :: ps => max p.height (Property.heightOf ps)

end

/-- The fuel that the function for each level uses besides nine units for
each level of nesting. -/
@[simp] def Level.cost : Level → Nat
  | .assign => 8 | .cond => 7 | .bin _ => 6 | .unary => 5 | .postfix => 4 | .lhs => 3 | .primary => 2

/-- The fuel that the parser's function for `level` needs to read `e`. -/
def need (level : Level) (e : Expr) : Nat := 9 * e.height + level.cost

/-- The parser's function for `level`. -/
def parseAt (f : Nat) : Level → ParseM Expr
  | .assign => Parse.parseAssign f
  | .cond => Parse.parseConditional f
  | .bin m => Parse.parseBinary f m
  | .unary => Parse.parseUnary f
  | .postfix => Parse.parsePostfix f
  | .lhs => Parse.parseLeftHandSide f
  | .primary => Parse.parsePrimary f

/-- What may follow `e` when the function for `level` reads it. A conditional
expression ends with an assignment expression, so an assignment cannot follow
it. -/
def Ends : Level → Expr → List Token → Prop
  | .assign, _ => EndsAssign
  | .cond, .cond .. => EndsAssign
  | .cond, _ => EndsCond
  | .bin m, e => fun rest => EndsBin m rest ∧ (e.endsInType = true → TypeOK rest)
  | .unary, _ | .postfix, _ => EndsPostfix
  | .lhs, _ => EndsLhs
  | .primary, _ => fun _ => True

/-- The function for each level reads every expression that is well formed
there, with fuel `f`. -/
def AllRead (T : Edition) (f : Nat) : Prop :=
  ∀ (level : Level) (e : Expr), e.wfAt T level = true → need level e ≤ f →
    ReadsE T (parseAt f level) e (Ends level e)

theorem ReadsW.weaken {α : Type} {T : Edition} {erase : α → α} {words : α → List Word}
    {afterOK : List TokenKind → α → Bool} {p : ParseM α} {x : α} {E E' : List Token → Prop}
    (h : ReadsW T erase words afterOK p x E) (hE : ∀ r, E' r → E r) : ReadsW T erase words afterOK p x E' :=
  fun s ts rest hT hs hl ht hn hr he ha => h s ts rest hT hs hl ht hn hr (hE rest he) ha

/-! ### Lists -/

/-- What follows an item of a list that `close` ends: a `,` or the `close`. -/
def EndsItem (close : String) (rest : List Token) : Prop :=
  ∃ u r, rest = u :: r ∧ (u.kind = .punct "," ∨ u.kind = .punct close)

/-- `afterOK` for each item of a list, which `close` follows. -/
def ListAfter {α : Type} (afterOK : List TokenKind → α → Bool) (tokens : α → List TokenKind)
    (close : List TokenKind) : List α → Prop
  | [] => True
  | [x] => afterOK close x = true
  | x :: y :: rest => afterOK (.punct "," :: joined "," ((y :: rest).map tokens) ++ close) x = true ∧
      ListAfter afterOK tokens close (y :: rest)

theorem Touching.nil {ts : List Token} : Touching ts [] ↔ ts = [] := by simp [Touching]

/-- The loop of a list in `open … close`: it reads each item with `p`, and a
`,` between two items, and stops before the `close`. -/
theorem iterate_list {α : Type} {T : Edition} {erase : α → α} {words : α → List Word}
    {afterOK : List TokenKind → α → Bool} {p : ParseM α} {close : String} {refuse : Token → ParseM Unit}
    (hclose : close ≠ ",") :
    ∀ (items : List α) (fuel : Nat) (acc : Array α) (s : ParseState) (ts rest : List Token) (c : Token),
      (∀ x ∈ items, ReadsW T erase words afterOK p x (EndsItem close)) →
      (∀ x ∈ items, ∃ k, (words x).flatten.head? = some k ∧ k ≠ .punct close ∧
        ∀ (t : Token) s, t.kind = k → refuse t s = .ok () s) →
      items.length < fuel → s.target = T →
      s.rest = ts ++ c :: rest → c.kind = .punct close → s.left = s.rest.length →
      Touching ts (separated "," (items.map words)) → (∀ y ∈ ts, NoBreak y) →
      ListAfter afterOK (fun x => (words x).flatten) (.punct close :: rest.map (·.kind)) items →
      ∃ res s', Parse.iterate fuel acc (Parse.listStep close refuse p) s = .ok res s' ∧
        res.toList.map erase = (acc.toList ++ items).map erase ∧ Leaves s s' (c :: rest) := by
  intro items
  induction items with
  | nil =>
    intro fuel acc s ts rest c _ _ hlen _ hs hc hl ht _ _
    obtain ⟨f', rfl⟩ : ∃ f', fuel = f' + 1 := ⟨fuel - 1, by simp at hlen; omega⟩
    have hts : ts = [] := Touching.nil.mp (by simpa [separated] using ht)
    subst hts
    have hs' : s.rest = c :: rest := by simpa using hs
    refine ⟨acc, s, Parse.iterate_false ?_, by simp, Leaves.refl hs' (by simp [hl, hs'])⟩
    simp [Parse.listStep, Parse.peek_eq hs', Token.isPunct, hc, bind, EStateM.bind, pure, EStateM.pure]
  | cons x items ih =>
    intro fuel acc s ts rest c hreads hstart hlen hT hs hc hl ht hn hafter
    obtain ⟨f', rfl⟩ : ∃ f', fuel = f' + 1 := ⟨fuel - 1, by simp at hlen; omega⟩
    obtain ⟨k, hk, hkc, hrefuse⟩ := hstart x (by simp)
    -- The tokens of `x`, and what follows them.
    obtain ⟨xts, more, rfl, hxt, hmore⟩ : ∃ xts more, ts = xts ++ more ∧ Touching xts (words x) ∧
        Touching more (if items = [] then [] else punctWord "," :: separated "," (items.map words)) := by
      cases items with
      | nil => exact ⟨ts, [], by simp, by simpa [separated] using ht, by simp [Touching]⟩
      | cons y ys =>
        have := Touching.append_split (ws₁ := words x) (ws₂ := punctWord "," :: separated "," ((y :: ys).map words))
          (by simpa [separated] using ht)
        simpa using this
    obtain ⟨t, xts', rfl⟩ : ∃ t xts', xts = t :: xts' := by
      have hk' := hxt.kinds
      cases xts with
      | nil => rw [← hk'] at hk; simp at hk
      | cons t xts' => exact ⟨t, xts', rfl⟩
    have htk : t.kind = k := by
      have hk' := hxt.kinds; rw [← hk'] at hk; simpa using hk
    have hs' : s.rest = t :: (xts' ++ more ++ c :: rest) := by simpa using hs
    have hkc' : t.kind ≠ .punct close := htk ▸ hkc
    -- The item.
    have hends : EndsItem close (more ++ c :: rest) := by
      cases items with
      | nil => simp [Touching] at hmore; subst hmore; exact ⟨c, rest, rfl, .inr hc⟩
      | cons y ys =>
        obtain ⟨d, more', rfl, hd, _⟩ := Touching.cons_one (by simpa [punctWord] using hmore)
        exact ⟨d, _, rfl, .inl hd⟩
    have hafter₁ : afterOK ((more ++ c :: rest).map (·.kind)) x = true := by
      cases items with
      | nil => simp [Touching] at hmore; subst hmore; simpa [ListAfter, hc] using hafter
      | cons y ys =>
        have := hmore.kinds
        simp only [if_neg (List.cons_ne_nil y ys)] at this
        simp only [ListAfter] at hafter
        rw [List.map_append, this]
        simpa [punctWord, separated_flatten, List.map_map, Function.comp_def, hc] using hafter.1
    obtain ⟨x', s₁, hp, he, hL⟩ := hreads x (by simp) s (t :: xts') (more ++ c :: rest) hT (by simp [hs'])
      hl hxt (fun y hy => hn y (by simp at hy ⊢; simp [hy])) (by simp) hends hafter₁
    have hT₁ : s₁.target = T := hL.target_eq.trans hT
    have hl₁ : s₁.left = s₁.rest.length := by rw [hL.left_eq, hL.rest_eq]
    cases items with
    | nil =>
      simp [Touching] at hmore; subst hmore
      have hs₁ : s₁.rest = c :: rest := by simpa using hL.rest_eq
      obtain ⟨res, s', hit, he', hL'⟩ := ih f' (acc.push x') s₁ [] rest c (by simp) (by simp)
        (by simp at hlen ⊢; omega) hT₁ (by simpa using hs₁) hc hl₁ (by simp [separated, Touching]) (by simp)
        (by simp [ListAfter])
      refine ⟨res, s', ?_, ?_, leaves_trans hL hL'⟩
      · rw [Parse.iterate_true (acc' := acc.push x') (s' := s₁)]
        · exact hit
        · have hcc : c.kind ≠ .punct "," := by rw [hc]; exact punct_ne hclose
          simp [Parse.listStep, Parse.peek_eq hs', Token.isPunct, hkc', hrefuse t s htk, hp,
            Parse.peek_eq hs₁, hc, hclose, bind, EStateM.bind, pure, EStateM.pure]
      · rw [he']; simp [he]
    | cons y ys =>
      obtain ⟨d, more', rfl, hd, hmore'⟩ := Touching.cons_one (by simpa [punctWord] using hmore)
      have hs₁ : s₁.rest = d :: (more' ++ c :: rest) := by simpa using hL.rest_eq
      let s₂ : ParseState := { s₁ with rest := more' ++ c :: rest, left := s₁.left - 1, lastStop := d.span.stop }
      have hl₂ : s₂.left = s₂.rest.length := by simp [s₂, hl₁, hs₁]
      simp only [ListAfter] at hafter
      obtain ⟨res, s', hit, he', hL'⟩ := ih f' (acc.push x') s₂ more' rest c
        (fun z hz => hreads z (by simp [hz])) (fun z hz => hstart z (by simp [hz]))
        (by simp at hlen ⊢; omega) hT₁ rfl hc hl₂ hmore'
        (fun z hz => hn z (by simp [hz])) hafter.2
      refine ⟨res, s', ?_, ?_, leaves_trans hL (leaves_trans (leaves_advance hs₁ hl₁) hL')⟩
      · rw [Parse.iterate_true (acc' := acc.push x') (s' := s₂)]
        · exact hit
        · simp [Parse.listStep, Parse.peek_eq hs', Token.isPunct, hkc', hrefuse t s htk, hp,
            Parse.peek_eq hs₁, hd, discard, Functor.mapConst, Function.comp_apply, EStateM.map,
            Parse.advance_cons hs₁ (by simp), s₂, bind, EStateM.bind, pure, EStateM.pure]
      · rw [he']; simp [he]


/-! ### Lists of expressions and properties -/

theorem Expr.wordsOf_eq (es : List Expr) : Expr.wordsOf es = es.map Expr.words := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [Expr.wordsOf, ih]

theorem Property.wordsOf_eq (ps : List Property) : Property.wordsOf ps = ps.map Property.words := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [Property.wordsOf, ih]

theorem Expr.eraseAll_eq (es : List Expr) : Expr.eraseAll es = es.map Expr.erase := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [Expr.eraseAll, ih]

theorem Property.eraseAll_eq (ps : List Property) : Property.eraseAll ps = ps.map Property.erase := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [Property.eraseAll, ih]

theorem Expr.listAfter {close : List TokenKind} :
    ∀ es : List Expr, Expr.afterOKList close es = true →
      ListAfter (fun after e => e.afterOK after) (fun e => e.words.flatten) close es
  | [], _ => trivial
  | [e], h => by simpa [Expr.afterOKList, ListAfter] using h
  | e :: f :: es, h => by
    simp only [Expr.afterOKList, Bool.and_eq_true] at h
    exact ⟨by simpa [Expr.tokens] using h.1, Expr.listAfter (f :: es) h.2⟩

theorem Property.listAfter {close : List TokenKind} :
    ∀ ps : List Property, Property.afterOKList close ps = true →
      ListAfter (fun after q => q.afterOK after) (fun q => q.words.flatten) close ps
  | [], _ => trivial
  | [q], h => by simpa [Property.afterOKList, ListAfter] using h
  | q :: r :: ps, h => by
    simp only [Property.afterOKList, Bool.and_eq_true] at h
    exact ⟨by simpa [Property.tokens] using h.1, Property.listAfter (r :: ps) h.2⟩

/-- The items of a list, with a `,` between two of them, are no more than its
tokens and one. -/
theorem length_items {α : Type} {words : α → List Word} {items : List α} {ts : List Token}
    (h : Touching ts (separated "," (items.map words))) : items.length ≤ ts.length + 1 := by
  have hk := congrArg List.length h.kinds
  rw [List.length_map, separated_flatten] at hk
  have := length_joined "," ((items.map words).map List.flatten)
  rw [← hk] at this
  simpa using this

/-- An expression starts with a token that is not a `close` of a list, and
that `refuse` lets through. -/
theorem Expr.start {close : String} {refuse : Token → ParseM Unit} (hclose : close ∈ [")", "]", "}"])
    (hrefuse : ∀ (t : Token) s, startsExpr t.kind = true → refuse t s = .ok () s) (e : Expr) :
    ∃ k, e.words.flatten.head? = some k ∧ k ≠ .punct close ∧
      ∀ (t : Token) s, t.kind = k → refuse t s = .ok () s := by
  obtain ⟨k, hk, hs⟩ := Expr.first e
  refine ⟨k, hk, ?_, fun t s ht => hrefuse t s (ht ▸ hs)⟩
  rintro rfl
  simp at hclose
  rcases hclose with rfl | rfl | rfl <;> simp [startsExpr] at hs

theorem refuseElement_ok (t : Token) (s : ParseState) (h : startsExpr t.kind = true) :
    Parse.refuseElement t s = .ok () s := by
  have h2 : t.kind ≠ .punct "," := by intro e; rw [e] at h; simp [startsExpr] at h
  simp [Parse.refuseElement, Token.isPunct, h2, pure, EStateM.pure]

/-- A `,` or a `close` ends an assignment expression. -/
theorem endsItem_assign {close : String} (hclose : close ∈ [")", "]", "}"]) {rest : List Token}
    (h : EndsItem close rest) : EndsAssign rest := by
  obtain ⟨u, r, rfl, hu | hu⟩ := h
  · exact endsAssign_separator hu (by simp [separators])
  · simp at hclose
    exact endsAssign_separator hu (by rcases hclose with rfl | rfl | rfl <;> simp [separators])

/-- The tokens `open`, then `inner`, then `close`. -/
theorem Touching.enclosed {ts : List Token} {o c : String} {inner : List Word}
    (h : Touching ts (punctWord o :: inner ++ [punctWord c])) :
    ∃ lp its rp, ts = lp :: (its ++ [rp]) ∧ lp.kind = .punct o ∧ Touching its inner ∧ rp.kind = .punct c := by
  obtain ⟨lp, ts₁, rfl, hlp, h₁⟩ := Touching.cons_one (by simpa [punctWord] using h)
  obtain ⟨its, ts₂, rfl, hits, h₂⟩ := Touching.append_split h₁
  obtain ⟨rp, ts₃, rfl, hrp, h₃⟩ := Touching.cons_one (by simpa [punctWord] using h₂)
  simp [Touching] at h₃; subst h₃
  exact ⟨lp, its, rp, rfl, hlp, hits, hrp⟩

theorem Parse.pure_bind {α β : Type} (a : α) (f : α → ParseM β) (s : ParseState) :
    ((pure a : ParseM α) >>= f) s = f a s := rfl

theorem Parse.pure_eq {α : Type} (a : α) (s : ParseState) : (pure a : ParseM α) s = .ok a s := rfl

theorem Parse.discard_eq {α : Type} {x : ParseM α} {s s' : ParseState} {a : α} (h : x s = .ok a s') :
    (discard x) s = .ok () s' := by
  simp [discard, Functor.mapConst, Function.comp_apply, EStateM.map, h]

/-- A check that the do notation writes as `if c then A; k else k`, where `A`
passes whenever `c` holds. -/
theorem Parse.ite_guard {β : Type} {c : Bool} {A : ParseM PUnit} {k : PUnit → ParseM β} {s : ParseState}
    (hA : c = true → A s = .ok () s) :
    (if c = true then A >>= k else pure PUnit.unit >>= k) s = k () s := by
  split
  · rename_i h; exact Parse.bind_eq (hA h)
  · rfl

/-! ### Elements and arguments -/

/-- `e` starts with the token that `o` starts with. -/
theorem head_of_first {e o : Expr} (he : ∀ k, o.tokens.head? = some k → e.tokens.head? = some k)
    (ih : o.tokens.head? ≠ some (.punct "...")) : e.tokens.head? ≠ some (.punct "...") := by
  obtain ⟨k, hk, -⟩ := Expr.first o
  rw [he k hk]
  rwa [hk] at ih

/-- No well-formed expression starts with `...`. `wfAt` refuses a spread at
every level, and only `parseElement` reads one. -/
theorem Expr.head_wf {T : Edition} : ∀ (e : Expr) (level : Level), e.wfAt T level = true →
    e.tokens.head? ≠ some (.punct "...")
  | .spread .., level, h => by cases level <;> simp [Expr.wfAt] at h
  | .member _ o _, level, h | .index _ o _, level, h | .call _ o _, level, h
  | .optMember _ o _, level, h | .postfix _ _ o, level, h => by
    have ho : o.wfAt T .lhs = true := by cases level <;> simp_all [Expr.wfAt]
    exact head_of_first (fun k hk => by simp [Expr.tokens, Expr.words] at hk ⊢; simp [hk])
      (Expr.head_wf o .lhs ho)
  | .binary _ _ o _, level, h | .asConst _ o, level, h | .satisfies _ o _, level, h => by
    have : ∃ level', o.wfAt T level' = true := by
      cases level <;> simp only [Expr.wfAt, Bool.and_eq_true] at h <;>
        first | exact ⟨_, h.1.1.1.1.2⟩ | exact ⟨_, h.1.2⟩ | exact ⟨_, h.1.1.2⟩ | simp_all
    obtain ⟨level', ho⟩ := this
    exact head_of_first (fun k hk => by simp [Expr.tokens, Expr.words] at hk ⊢; simp [hk])
      (Expr.head_wf o level' ho)
  | .cond _ o _ _, level, h => by
    have : o.wfAt T (.bin 0) = true := by
      cases level <;> simp [Expr.wfAt] at h <;> first | exact h.1.1.1 | simp_all [Expr.wfAt]
    exact head_of_first (fun k hk => by simp [Expr.tokens, Expr.words] at hk ⊢; simp [hk])
      (Expr.head_wf o (.bin 0) this)
  | .assign _ _ o _, level, h => by
    have : o.wfAt T .cond = true := by
      cases level <;> simp [Expr.wfAt] at h <;> first | exact h.1.1.1 | simp_all [Expr.wfAt]
    exact head_of_first (fun k hk => by simp [Expr.tokens, Expr.words] at hk ⊢; simp [hk])
      (Expr.head_wf o .cond this)
  | .arrow _ parens ps _, _, _ => by
    rcases arrowParams_cases parens ps with ⟨p, _, _, hp⟩ | hp <;>
      simp [Expr.tokens, Expr.words, hp, identWord, enclose, punctWord]
  | .unary _ op _, _, _ => by
    cases op <;> simp [Expr.tokens, Expr.words, UnaryOp.symbol, symbol, Lex.reservedWords, punctWord, keywordWord]
  | .prefix _ op _, _, _ => by cases op <;> simp [Expr.tokens, Expr.words, UpdateOp.symbol, punctWord]
  | .ident .., _, _ | .number .., _, _ | .bigint .., _, _ | .string .., _, _ | .bool .., _, _
  | .null _, _, _ | .array .., _, _ | .object .., _, _ | .paren .., _, _ | .new .., _, _ => by
    simp [Expr.tokens, Expr.words, identWord, keywordWord, enclose, punctWord]

/-- An element, when `item` reads the value of a spread, and reads any other
element itself. -/
theorem parseElement_reads {T : Edition} {item : ParseM Expr} {ends : List Token → Prop} (x : Expr)
    (hx : x.elemWF T = true)
    (hv : ∀ sp v, x = .spread sp v → ReadsE T item v ends)
    (hi : (∀ sp v, x ≠ .spread sp v) → ReadsE T item x ends) :
    ReadsE T (Parse.parseElement item) x ends := by
  intro s ts rest hT hs hl ht hn hr hE ha
  by_cases hsp : ∃ sp v, x = .spread sp v
  · obtain ⟨sp, v, rfl⟩ := hsp
    obtain ⟨x, vts, rfl, hx, hv'⟩ := Touching.cons_one (by simpa [Expr.words, punctWord] using ht)
    have hs' : s.rest = x :: (vts ++ rest) := by simpa using hs
    let s₁ := past s x (vts ++ rest)
    have hl₁ : s₁.left = s₁.rest.length := by simp [s₁, hl, hs']
    obtain ⟨v', s₂, hp, he, hL⟩ := hv sp v rfl s₁ vts rest hT rfl hl₁ hv'
      (fun y hy => hn y (by simp [List.mem_of_mem_tail hy])) hr hE (by simpa [Expr.afterOK] using ha)
    refine ⟨.spread ⟨x.span.start, s₂.lastStop⟩ v', s₂, ?_, by simp [Expr.erase, he],
      leaves_trans (leaves_advance hs' hl) hL⟩
    simp only [Parse.parseElement]
    rw [Parse.bind_eq (Parse.peek_eq hs'), if_pos (by simp [Token.isPunct, hx]),
      Parse.bind_eq (Parse.discard_eq (Parse.advance_cons hs' (by simp [hr]))), Parse.bind_eq hp,
      Parse.bind_eq (Parse.spanFrom_eq _ _)]
    rfl
  · have hne : ∀ sp v, x ≠ .spread sp v := fun sp v h => hsp ⟨sp, v, h⟩
    have hw : x.wfAt T .assign = true := by
      cases x <;> first | exact absurd rfl (hne _ _) | simpa [Expr.elemWF] using hx
    obtain ⟨k, hk, -⟩ := Expr.first x
    have hkinds : (ts.map (·.kind)).head? = some k := by rw [ht.kinds]; exact hk
    obtain ⟨y, ts', rfl⟩ : ∃ y ts', ts = y :: ts' := by
      cases ts with
      | nil => simp at hkinds
      | cons y ts' => exact ⟨y, ts', rfl⟩
    have hy : y.kind ≠ .punct "..." := by
      have h1 := Expr.head_wf x .assign hw
      simp only [List.map_cons, List.head?_cons, Option.some.injEq] at hkinds
      rw [hk, ← hkinds] at h1
      intro e; exact h1 (by rw [e])
    obtain ⟨x', s', hp, he, hL⟩ := hi hne s (y :: ts') rest hT hs hl ht hn hr hE ha
    refine ⟨x', s', ?_, he, hL⟩
    simp only [Parse.parseElement]
    rw [Parse.bind_eq (Parse.peek_eq (show s.rest = y :: (ts' ++ rest) by simpa using hs)),
      if_neg (by simp [Token.isPunct, hy])]
    exact hp

/-- An element that is not a spread is an assignment expression. -/
theorem Expr.elemWF_eq {T : Edition} {x : Expr} (hne : ∀ sp v, x ≠ .spread sp v) :
    x.elemWF T = x.wfAt T .assign := by
  cases x <;> first | exact absurd rfl (hne _ _) | simp [Expr.elemWF]

/-- An element, when `parseAssign` reads each well-formed expression no
higher than it. -/
theorem parseElement_of {T : Edition} {g : Nat} {x : Expr} (hx : x.elemWF T = true)
    (IH : ∀ v, v.wfAt T .assign = true → v.height ≤ x.height → ReadsE T (Parse.parseAssign g) v EndsAssign) :
    ReadsE T (Parse.parseElement (Parse.parseAssign g)) x EndsAssign :=
  parseElement_reads x hx
    (fun sp v h => by subst h; exact IH v (by simpa [Expr.elemWF] using hx) (by simp [Expr.height]))
    (fun hne => IH x (by rw [← Expr.elemWF_eq hne]; exact hx) (Nat.le_refl _))

/-! ### Fuel for a type -/

theorem TypeExpr.tokens_paren (sp : Span) (i : TypeExpr) :
    (TypeExpr.paren sp i).tokens = .punct "(" :: i.tokens ++ [.punct ")"] := by
  simp [TypeExpr.tokens, TypeExpr.words, punctWord]

theorem TypeExpr.tokens_array (sp : Span) (e : TypeExpr) :
    (TypeExpr.array sp e).tokens = e.tokens ++ [.punct "[", .punct "]"] := by
  simp [TypeExpr.tokens, TypeExpr.words, punctWord]

mutual

/-- A type nests no deeper than it has tokens. -/
theorem TypeExpr.height_le : ∀ t : TypeExpr, t.height ≤ t.tokens.length
  | .predicate _ _ target => by
    have h := TypeExpr.height_le target
    simp [TypeExpr.height, TypeExpr.tokens, TypeExpr.words, identWord] at h ⊢
    omega
  | .ref _ _ [] => by simp [TypeExpr.height, TypeExpr.heightOf, TypeExpr.tokens, TypeExpr.words, identWord]
  | .ref sp n (a :: as) => by
    have := TypeExpr.heightOf_le (a :: as)
    rw [tokens_ref sp n _ (by simp)]
    simp only [TypeExpr.height, List.length_cons, List.length_append, List.length_nil]; omega
  | .paren sp i => by
    have := TypeExpr.height_le i
    rw [TypeExpr.tokens_paren]; simp only [TypeExpr.height, List.length_cons, List.length_append, List.length_nil]
    omega
  | .array sp e => by
    have := TypeExpr.height_le e
    rw [TypeExpr.tokens_array]; simp only [TypeExpr.height, List.length_cons, List.length_append, List.length_nil]
    omega
  | .union _ [] => by simp [TypeExpr.height, TypeExpr.heightOf]
  | .union sp [m] => by
    have := TypeExpr.height_le m
    rw [tokens_union_one]; simp only [TypeExpr.height, TypeExpr.heightOf, List.length_cons]; omega
  | .union sp (m₁ :: m₂ :: ms) => by
    have := TypeExpr.height_le m₁; have := TypeExpr.heightOf_le_bars (m₂ :: ms)
    rw [tokens_union]
    simp only [TypeExpr.height, TypeExpr.heightOf, List.length_append] at this ⊢; omega
  | .tuple sp false es => by
    have := TypeExpr.heightOf_le es
    rw [tokens_tuple]; simp only [TypeExpr.height, List.length_cons, List.length_append, List.length_nil]
    simp; omega
  | .tuple sp true es => by
    have := TypeExpr.heightOf_le es
    rw [tokens_readonly, tokens_tuple]
    simp only [TypeExpr.height, List.length_cons, List.length_append, List.length_nil]
    simp; omega
  | .keyword .. | .null _ | .literal .. => by simp [TypeExpr.height]

theorem TypeExpr.heightOf_le : ∀ ts : List TypeExpr, TypeExpr.heightOf ts ≤ (joined "," (ts.map TypeExpr.tokens)).length
  | [] => by simp [TypeExpr.heightOf, joined]
  | [t] => by have := TypeExpr.height_le t; simp [TypeExpr.heightOf, joined]; omega
  | t :: u :: ts => by
    have := TypeExpr.height_le t; have := TypeExpr.heightOf_le (u :: ts)
    show max t.height (TypeExpr.heightOf (u :: ts)) ≤
      (t.tokens ++ .punct "," :: joined "," ((u :: ts).map TypeExpr.tokens)).length
    simp only [List.length_append, List.length_cons]; omega

theorem TypeExpr.heightOf_le_bars : ∀ ts : List TypeExpr,
    TypeExpr.heightOf ts ≤ (ts.map fun i => .punct "|" :: i.tokens).flatten.length
  | [] => by simp [TypeExpr.heightOf]
  | t :: ts => by
    have := TypeExpr.height_le t; have := TypeExpr.heightOf_le_bars ts
    simp only [TypeExpr.heightOf, List.map_cons, List.flatten_cons, List.length_append, List.length_cons]
    omega

end

/-- `parseType`, with the fuel that `budget` gives, reads every type. -/
theorem parseType_budget (t : TypeExpr) (ht : t.wf = true) :
    ∀ (s : ParseState) (ts rest : List Token), s.rest = ts ++ rest → s.left = s.rest.length →
      ts.map (·.kind) = t.tokens → (∀ y ∈ ts, NoBreak y) → rest ≠ [] → FollowsType rest →
      ∃ t' s', Parse.parseType (10 * (s.left + 1)) s = .ok t' s' ∧ t'.erase = t.erase ∧ Leaves s s' rest := by
  intro s ts rest hs hl hk hn hr hf
  have h1 := TypeExpr.height_le t
  have h2 : ts.length = t.tokens.length := by rw [← hk, List.length_map]
  have h3 : ts.length ≤ s.left := by rw [hl, hs, List.length_append]; omega
  exact (types_reads _).1 t ht (by omega) s ts rest hs hl hk hn hr hf

/-- `parsePrimaryType` reads a primary type with the fuel that `budget` gives. -/
theorem parsePrimaryType_budget (t : TypeExpr) (ht : t.primaryWF = true) :
    ∀ (s : ParseState) (ts rest : List Token), s.rest = ts ++ rest → s.left = s.rest.length →
      ts.map (·.kind) = t.tokens → (∀ y ∈ ts, NoBreak y) → rest ≠ [] → FollowsPrimary rest →
      ∃ t' s', Parse.parsePrimaryType (10 * (s.left + 1)) s = .ok t' s' ∧ t'.erase = t.erase ∧
        Leaves s s' rest := by
  intro s ts rest hs hl hk hn hr hf
  have h1 := TypeExpr.height_le t
  have h2 : ts.length = t.tokens.length := by rw [← hk, List.length_map]
  have h3 : ts.length ≤ s.left := by rw [hl, hs, List.length_append]; omega
  exact (types_reads _).2.2 t ht (by omega) s ts rest hs hl hk hn hr hf


/-! ### Parameters -/

theorem readName_ok {s : ParseState} {x u : Token} {r : List Token} {name : String}
    (hs : s.rest = x :: u :: r) (hx : x.kind = .ident name) (hn : name ∉ Parse.refusedNames) :
    Parse.readName s = .ok name (past s x (u :: r)) := by
  simp [Parse.readName, Parse.advance_eq hs, hx, hn, bind, EStateM.bind, pure, EStateM.pure]

/-- A parameter's type ends before `,` or `)`. -/
theorem followsType_item {u : Token} {r : List Token} (hu : u.kind = .punct "," ∨ u.kind = .punct ")") :
    FollowsType (u :: r) := by
  rcases hu with hu | hu <;> exact followsType_punct hu (by simp)

theorem readName_ok' {s : ParseState} {x : Token} {r : List Token} {name : String}
    (hs : s.rest = x :: r) (hr : r ≠ []) (hx : x.kind = .ident name) (hn : name ∉ Parse.refusedNames) :
    Parse.readName s = .ok name (past s x r) := by
  obtain ⟨u, r', rfl⟩ := List.exists_cons_of_ne_nil hr
  exact readName_ok hs hx hn

/-- `readOptionalMark` reads nothing before a token other than `?`. -/
theorem readOptionalMark_none {ok : Bool} {s : ParseState} {u : Token} {r : List Token}
    (hs : s.rest = u :: r) (hu : u.kind ≠ .punct "?") : Parse.readOptionalMark ok s = .ok false s := by
  simp only [Parse.readOptionalMark]
  rw [Parse.bind_eq (Parse.peek_eq hs), if_neg (by simp [Token.isPunct, hu])]
  rfl

/-- `readOptionalMark` reads a `?` where an optional parameter may stand. -/
theorem readOptionalMark_some {s : ParseState} {q : Token} {r : List Token}
    (hs : s.rest = q :: r) (hr : r ≠ []) (hq : q.kind = .punct "?") :
    Parse.readOptionalMark true s = .ok true (past s q r) := by
  simp only [Parse.readOptionalMark]
  rw [Parse.bind_eq (Parse.peek_eq hs), if_pos (by simp [Token.isPunct, hq])]
  rw [Parse.ite_guard (fun h => by simp at h)]
  rw [Parse.bind_eq (Parse.discard_eq (Parse.advance_cons hs hr))]
  rfl

theorem parseParam_reads {T : Edition} {ok : Bool} (p : Param) (hp : p.wf = true)
    (hopt : p.optional = true → ok = true) :
    ReadsW T Param.erase Param.words (fun _ _ => true) (Parse.parseParam ok) p (EndsItem ")") := by
  intro s ts rest _ hs hl ht hn hr hE _
  obtain ⟨sp, name, optional, type⟩ := p
  simp only [Param.wf, Bool.and_eq_true] at hp
  obtain ⟨hname, hty⟩ := hp
  have hname' : name ∉ Parse.refusedNames := by simpa [exprName] using hname
  obtain ⟨u, r, rfl, hu⟩ := hE
  have hu1 : u.kind ≠ .punct "?" := by rcases hu with h | h <;> rw [h] <;> exact punct_ne (by decide)
  have hu2 : u.kind ≠ .punct "=" := by rcases hu with h | h <;> rw [h] <;> exact punct_ne (by decide)
  have hu3 : u.kind ≠ .punct ":" := by rcases hu with h | h <;> rw [h] <;> exact punct_ne (by decide)
  simp only [Param.words] at ht
  obtain ⟨nm, ts', rfl, hnm, h'⟩ := Touching.cons_one (by simpa [identWord] using ht)
  have hn1 : nm.kind ≠ .punct "..." ∧ nm.kind ≠ .punct "[" ∧ nm.kind ≠ .punct "{" ∧ nm.kind ≠ .keyword "this" := by
    rw [hnm]; simp
  have hs' : s.rest = nm :: (ts' ++ u :: r) := by simpa using hs
  have hl₀ : (past s nm (ts' ++ u :: r)).left = (past s nm (ts' ++ u :: r)).rest.length := by simp [hl, hs']
  -- The `?` of an optional parameter, and then the tokens of its type.
  obtain ⟨tts, s₁, hmark, hs₁, hl₁, hL₁, htt, hsub⟩ : ∃ tts s₁,
      Parse.readOptionalMark ok (past s nm (ts' ++ u :: r)) = .ok optional s₁ ∧
      s₁.rest = tts ++ u :: r ∧ s₁.left = s₁.rest.length ∧ Leaves s s₁ (tts ++ u :: r) ∧
      Touching tts (typeAnnotation type) ∧ ∀ y ∈ tts, y ∈ ts' := by
    cases optional with
    | false =>
      have hfirst : ∀ y, (ts' ++ u :: r).head? = some y → y.kind ≠ .punct "?" := by
        intro y hy
        cases type with
        | none =>
          simp [Touching, optionalMark, typeAnnotation] at h'; subst h'
          simp at hy; subst hy; exact hu1
        | some t =>
          obtain ⟨colon, ts₂, rfl, hcolon, -⟩ :=
            Touching.cons_one (by simpa [punctWord, typeAnnotation, optionalMark] using h')
          simp at hy; subst hy; rw [hcolon]; exact punct_ne (by decide)
      obtain ⟨y, r', hyr⟩ : ∃ y r', ts' ++ u :: r = y :: r' := List.exists_cons_of_ne_nil (by simp)
      refine ⟨ts', _, readOptionalMark_none (u := y) (r := r') (s := past s nm (ts' ++ u :: r)) (by simp [hyr])
        (hfirst y (by simp [hyr])), rfl, hl₀, leaves_advance hs' hl, by simpa [optionalMark] using h',
        fun _ h => h⟩
    | true =>
      obtain ⟨q, tts, rfl, hq, htt⟩ := Touching.cons_one (by simpa [optionalMark, punctWord] using h')
      refine ⟨tts, _, ?_, rfl, by simp [hl, hs'], leaves_trans (leaves_advance hs' hl)
        (leaves_advance (s := past s nm (q :: (tts ++ u :: r))) rfl hl₀), htt, fun _ h => by simp [h]⟩
      rw [hopt rfl]
      exact readOptionalMark_some rfl (by simp) hq
  have hnr : ts' ++ u :: r ≠ [] := by simp
  cases type with
  | none =>
    simp [Touching, typeAnnotation] at htt; subst htt
    simp only [List.nil_append] at hs₁ hL₁
    refine ⟨⟨⟨nm.span.start, s₁.lastStop⟩, name, optional, none⟩, s₁, ?_, rfl, hL₁⟩
    simp only [Parse.parseParam]
    rw [Parse.bind_eq (Parse.peek_eq hs')]
    rw [Parse.ite_guard (fun h => by simp [Token.isPunct, hn1] at h),
      Parse.ite_guard (fun h => by simp [Token.isPunct, hn1] at h),
      Parse.ite_guard (fun h => by simp [Token.isKeyword, hn1] at h)]
    rw [Parse.bind_eq (readName_ok' hs' hnr hnm hname'), Parse.bind_eq hmark, Parse.bind_eq (Parse.peek_eq hs₁)]
    rw [if_neg (by simp [Token.isPunct, hu3]), Parse.pure_bind, Parse.bind_eq (Parse.peek_eq hs₁)]
    rw [Parse.ite_guard (fun h => by simp [Token.isPunct, hu2] at h)]
    rw [Parse.bind_eq (Parse.spanFrom_eq _ _)]
    rfl
  | some t =>
    obtain ⟨colon, ts₂, rfl, hcolon, h₂⟩ := Touching.cons_one (by simpa [punctWord, typeAnnotation] using htt)
    let s₂ := past s₁ colon (ts₂ ++ u :: r)
    have hl₂ : s₂.left = s₂.rest.length := by simp [s₂, hl₁, hs₁]
    obtain ⟨t', s₃, hpt, het, hL₃⟩ := parseType_budget t (by simpa using hty) s₂ ts₂ (u :: r) rfl hl₂ h₂.kinds
      (fun y hy => hn y (by simpa using hsub y (by simp [hy]))) (by simp) (followsType_item hu)
    have hs₃ : s₃.rest = u :: r := hL₃.rest_eq
    refine ⟨⟨⟨nm.span.start, s₃.lastStop⟩, name, optional, some t'⟩, s₃, ?_, by simp [Param.erase, het],
      leaves_trans hL₁ (leaves_trans (leaves_advance (s := s₁) (by simpa using hs₁) hl₁) hL₃)⟩
    simp only [Parse.parseParam]
    rw [Parse.bind_eq (Parse.peek_eq hs')]
    rw [Parse.ite_guard (fun h => by simp [Token.isPunct, hn1] at h),
      Parse.ite_guard (fun h => by simp [Token.isPunct, hn1] at h),
      Parse.ite_guard (fun h => by simp [Token.isKeyword, hn1] at h)]
    rw [Parse.bind_eq (readName_ok' hs' hnr hnm hname'), Parse.bind_eq hmark,
      Parse.bind_eq (Parse.peek_eq (by simpa using hs₁))]
    rw [if_pos (by simp [Token.isPunct, hcolon])]
    rw [Parse.bind_eq (Parse.discard_eq (Parse.advance_cons (s := s₁) (by simpa using hs₁) (by simp))),
      Parse.bind_eq (Parse.budget_eq _), Parse.bind_eq hpt, Parse.pure_bind, Parse.bind_eq (Parse.peek_eq hs₃)]
    rw [Parse.ite_guard (fun h => by simp [Token.isPunct, hu2] at h)]
    rw [Parse.bind_eq (Parse.spanFrom_eq _ _)]
    rfl


theorem listAfter_true {α : Type} {tokens : α → List TokenKind} {close : List TokenKind} :
    ∀ xs : List α, ListAfter (fun _ _ => true) tokens close xs
  | [] => trivial
  | [_] => rfl
  | _ :: y :: xs => ⟨rfl, listAfter_true (y :: xs)⟩

/-- `( params )`, which `listStep` and `parseParam` read. -/
theorem params_reads {T : Edition} {ok : Bool} (params : List Param) (hps : ∀ p ∈ params, p.wf = true)
    (hopt : ∀ p ∈ params, p.optional = true → ok = true)
    (s : ParseState) (its rest : List Token) (rp : Token) (hT : s.target = T) (hs : s.rest = its ++ rp :: rest)
    (hrp : rp.kind = .punct ")") (hl : s.left = s.rest.length)
    (ht : Touching its (separated "," (params.map Param.words))) (hn : ∀ y ∈ its, NoBreak y) :
    ∃ res s', Parse.iterate (10 * (s.left + 1)) #[] (Parse.listStep ")" (fun _ => pure ()) (Parse.parseParam ok)) s =
      .ok res s' ∧ res.toList.map Param.erase = params.map Param.erase ∧ Leaves s s' (rp :: rest) := by
  obtain ⟨res, s', hit, he, hL⟩ := iterate_list (close := ")") (refuse := fun _ => pure ()) (by decide)
    params (10 * (s.left + 1)) #[] s its rest rp (fun p hp => parseParam_reads p (hps p hp) (hopt p hp))
    (fun p _ => ⟨.ident p.name, by simp [Param.words, identWord], by simp, fun _ _ _ => rfl⟩)
    (by have := length_items ht; have : s.left = its.length + rest.length + 1 := by simp [hl, hs]; omega
        omega) hT hs hrp hl ht hn (listAfter_true params)
  exact ⟨res, s', hit, by simpa using he, hL⟩


/-- `( args )`, when `parseElement` reads each argument. -/
theorem parseArguments_reads {T : Edition} (g : Nat) (args : List Expr)
    (hargs : ∀ x ∈ args, ReadsE T (Parse.parseElement (Parse.parseAssign g)) x EndsAssign) :
    ∀ (s : ParseState) (ts rest : List Token), s.target = T → s.rest = ts ++ rest →
      s.left = s.rest.length → Touching ts (enclose "(" ")" (Expr.wordsOf args)) →
      (∀ y ∈ ts, NoBreak y) → rest ≠ [] →
      Expr.afterOKList (.punct ")" :: rest.map (·.kind)) args = true →
      ∃ args' s', Parse.parseArguments (g + 1) s = .ok args' s' ∧
        Expr.eraseAll args' = Expr.eraseAll args ∧ Leaves s s' rest := by
  intro s ts rest hT hs hl ht hn hr ha
  obtain ⟨lp, its, rp, rfl, hlp, hits, hrp⟩ := Touching.enclosed (by simpa [enclose] using ht)
  have hs₁ : s.rest = lp :: (its ++ rp :: rest) := by simpa using hs
  let s₁ : ParseState := { s with rest := its ++ rp :: rest, left := s.left - 1, lastStop := lp.span.stop }
  have hl₁ : s₁.left = s₁.rest.length := by simp [s₁, hl, hs₁]
  rw [Expr.wordsOf_eq] at hits
  obtain ⟨res, s₂, hit, he, hL⟩ := iterate_list (close := ")") (refuse := fun _ => pure ()) (by decide)
    args (10 * (s₁.left + 1)) #[] s₁ its rest rp
    (fun x hx => (hargs x hx).weaken fun r h => endsItem_assign (by simp) h)
    (fun x _ => Expr.start (by simp) (fun _ _ _ => rfl) x)
    (by have := length_items hits; have : s₁.left = its.length + rest.length + 1 := by simp [s₁, hl, hs₁]; omega
        omega) hT rfl hrp hl₁ hits
    (fun y hy => hn y (by simp [hy])) (Expr.listAfter args ha)
  have hs₂ : s₂.rest = rp :: rest := hL.rest_eq
  refine ⟨res.toList, { s₂ with rest := rest, left := s₂.left - 1, lastStop := rp.span.stop }, ?_, ?_,
    leaves_trans (leaves_advance hs₁ hl) (leaves_trans hL (leaves_advance hs₂ (by rw [hL.left_eq, hs₂])))⟩
  · simp only [Parse.parseArguments, bind, EStateM.bind, Parse.expectPunct_ok hs₁ (by simp) hlp]
    simp only [Parse.budget_eq]
    rw [show ({ s with rest := its ++ rp :: rest, left := s.left - 1, lastStop := lp.span.stop } : ParseState) = s₁
      from rfl, hit]
    simp [Parse.expectPunct_ok hs₂ hr hrp, pure, EStateM.pure]
  · simpa [Expr.eraseAll_eq] using he


/-- `[ elems ]`, when `parseElement` reads each element. -/
theorem parseArrayLiteral_reads {T : Edition} (g : Nat) (sp : Span) (elems : List Expr)
    (helems : ∀ x ∈ elems, ReadsE T (Parse.parseElement (Parse.parseAssign g)) x EndsAssign) :
    ReadsE T (Parse.parseArrayLiteral (g + 1)) (.array sp elems) (fun _ => True) := by
  intro s ts rest hT hs hl ht hn hr _ ha
  obtain ⟨lp, its, rp, rfl, hlp, hits, hrp⟩ := Touching.enclosed (by simpa [Expr.words, enclose] using ht)
  have hs₁ : s.rest = lp :: (its ++ rp :: rest) := by simpa using hs
  let s₁ : ParseState := { s with rest := its ++ rp :: rest, left := s.left - 1, lastStop := lp.span.stop }
  have hl₁ : s₁.left = s₁.rest.length := by simp [s₁, hl, hs₁]
  rw [Expr.wordsOf_eq] at hits
  obtain ⟨res, s₂, hit, he, hL⟩ := iterate_list (close := "]") (refuse := Parse.refuseElement) (by decide)
    elems (10 * (s₁.left + 1)) #[] s₁ its rest rp
    (fun x hx => (helems x hx).weaken fun r h => endsItem_assign (by simp) h)
    (fun x _ => Expr.start (by simp) refuseElement_ok x)
    (by have := length_items hits; have : s₁.left = its.length + rest.length + 1 := by simp [s₁, hl, hs₁]; omega
        omega) hT rfl hrp hl₁ hits
    (fun y hy => hn y (by simp [hy])) (Expr.listAfter elems (by simpa [Expr.afterOK] using ha))
  have hs₂ : s₂.rest = rp :: rest := hL.rest_eq
  let s₃ : ParseState := { s₂ with rest := rest, left := s₂.left - 1, lastStop := rp.span.stop }
  refine ⟨.array ⟨lp.span.start, s₃.lastStop⟩ res.toList, s₃, ?_, ?_,
    leaves_trans (leaves_advance hs₁ hl) (leaves_trans hL (leaves_advance hs₂ (by rw [hL.left_eq, hs₂])))⟩
  · simp only [Parse.parseArrayLiteral]
    rw [Parse.bind_eq (Parse.expectPunct_ok hs₁ (by simp) hlp), Parse.bind_eq (Parse.budget_eq _)]
    rw [Parse.bind_eq (s' := s₂) (a := res) hit, Parse.bind_eq (Parse.expectPunct_ok hs₂ hr hrp),
      Parse.bind_eq (Parse.spanFrom_eq _ _)]
    rfl
  · simpa [Expr.erase, Expr.eraseAll_eq] using he

/-- The name and the type arguments of a `new` are the words of a type
reference. -/
theorem typeArgWords_ref (sp : Span) (c : String) (ts : List TypeExpr) :
    identWord c :: typeArgWords ts = (TypeExpr.ref sp c ts).words := by
  cases ts <;> rfl

/-- `new C<A>(args)`, when `parseAssign` reads each argument. `C<A>` is read
as a type reference. -/
theorem parseNew_reads {T : Edition} (g : Nat) (sp : Span) (c : String) (targs : List TypeExpr)
    (args : List Expr) (hc : typeName c = true) (hts : TypeExpr.allWF targs = true)
    (hargs : ∀ x ∈ args, ReadsE T (Parse.parseElement (Parse.parseAssign g)) x EndsAssign) :
    ReadsE T (Parse.parseNew (g + 1 + 1)) (.new sp c targs args) (fun _ => True) := by
  intro s ts rest hT hs hl ht hn hr _ ha
  have hw : (Expr.new sp c targs args).words =
      [.keyword "new"] :: ((TypeExpr.ref sp c targs).words ++ enclose "(" ")" (Expr.wordsOf args)) := by
    rw [← typeArgWords_ref sp c targs]; rfl
  rw [hw] at ht
  obtain ⟨nw, ts₁, rfl, hnw, h₁⟩ := Touching.cons_one ht
  obtain ⟨tts, ats, rfl, htt, hat⟩ := Touching.append_split h₁
  obtain ⟨lp, its, rp, rfl, hlp, hits, hrp⟩ := Touching.enclosed (by simpa [enclose] using hat)
  -- The name, which the checks before the type read: no `.` follows it.
  obtain ⟨x₁, tts', htts, hx₁⟩ : ∃ x₁ tts', tts = x₁ :: tts' ∧ x₁.kind = .ident c := by
    have hk : tts.map (·.kind) = (TypeExpr.ref sp c targs).tokens := htt.kinds
    cases tts with
    | nil => cases targs <;> simp [TypeExpr.tokens, TypeExpr.words, identWord] at hk
    | cons x₁ tts' =>
      refine ⟨x₁, tts', rfl, ?_⟩
      cases targs with
      | nil => simp [TypeExpr.tokens, TypeExpr.words, identWord] at hk; exact hk.1
      | cons a as => rw [tokens_ref sp c (a :: as) (by simp)] at hk; simp at hk; exact hk.1
  obtain ⟨y, hy, hyk⟩ : ∃ y, (tts ++ lp :: (its ++ rp :: rest))[1]? = some y ∧ y.kind ≠ .punct "." := by
    have hk : tts.map (·.kind) = (TypeExpr.ref sp c targs).tokens := htt.kinds
    rw [htts] at hk ⊢
    cases tts' with
    | nil => exact ⟨lp, by simp, by rw [hlp]; exact punct_ne (by decide)⟩
    | cons x₂ _ =>
      refine ⟨x₂, by simp, ?_⟩
      cases targs with
      | nil => simp [TypeExpr.tokens, TypeExpr.words, identWord] at hk
      | cons a as =>
        rw [tokens_ref sp c (a :: as) (by simp)] at hk
        simp at hk; rw [hk.2.1]; exact punct_ne (by decide)
  have hs₀ : s.rest = nw :: (tts ++ lp :: (its ++ rp :: rest)) := by simpa using hs
  let s₁ := past s nw (tts ++ lp :: (its ++ rp :: rest))
  have hl₁ : s₁.left = s₁.rest.length := by simp [s₁, hl, hs₀]
  have hwf : (TypeExpr.ref sp c targs).primaryWF = true := by simp [TypeExpr.primaryWF, hc, hts]
  have hfp : FollowsPrimary (lp :: (its ++ rp :: rest)) := fun u hu => by
    simp at hu; subst hu; rw [hlp]; exact ⟨punct_ne (by decide), punct_ne (by decide)⟩
  obtain ⟨t', s₂, hpt, het, hL₂⟩ := parsePrimaryType_budget _ hwf s₁ tts (lp :: (its ++ rp :: rest)) rfl hl₁
    htt.kinds (fun y hy => hn y (by simp [hy])) (by simp) hfp
  obtain ⟨sp', targs', rfl, htargs⟩ : ∃ sp' targs', t' = .ref sp' c targs' ∧
      TypeExpr.eraseAll targs' = TypeExpr.eraseAll targs := by
    cases t' <;> simp [TypeExpr.erase] at het
    obtain ⟨rfl, h⟩ := het
    exact ⟨_, _, rfl, h⟩
  have hs₂ : s₂.rest = lp :: (its ++ rp :: rest) := hL₂.rest_eq
  have hl₂ : s₂.left = s₂.rest.length := by rw [hL₂.left_eq, hs₂]
  obtain ⟨args', s₃, hpa, hea, hL₃⟩ := parseArguments_reads g args hargs s₂ (lp :: (its ++ [rp])) rest
    (hL₂.target_eq.trans (by simpa [s₁] using hT)) (by simpa using hs₂) hl₂ (by simpa [enclose] using hat)
    (fun y hy => hn y (by simp at hy ⊢; rcases hy with h | h | h <;> simp [h])) hr
    (by simpa [Expr.afterOK] using ha)
  refine ⟨.new ⟨nw.span.start, s₃.lastStop⟩ c targs' args', s₃, ?_, ?_,
    leaves_trans (leaves_advance hs₀ hl) (leaves_trans hL₂ hL₃)⟩
  · simp only [Parse.parseNew]
    rw [Parse.bind_eq (Parse.advance_cons hs₀ (by simp))]
    rw [Parse.bind_eq (Parse.peek_eq (s := past s nw (tts ++ lp :: (its ++ rp :: rest)))
      (t := x₁) (r := tts' ++ lp :: (its ++ rp :: rest)) (by simp [htts]))]
    rw [Parse.ite_guard (fun h => by simp [hx₁] at h)]
    rw [Parse.bind_eq (Parse.peekAt_eq (s := past s nw (tts ++ lp :: (its ++ rp :: rest))) (k := 1) hy)]
    rw [Parse.ite_guard (fun h => by simp [Token.isPunct, hyk] at h)]
    rw [Parse.bind_eq (Parse.budget_eq _)]
    rw [Parse.bind_eq (s' := s₂) (a := TypeExpr.ref sp' c targs') hpt]
    simp only []
    rw [Parse.bind_eq (Parse.peek_eq hs₂)]
    rw [Parse.ite_guard (fun h => by simp [Token.isPunct, hlp] at h)]
    rw [Parse.bind_eq hpa, Parse.bind_eq (Parse.spanFrom_eq _ _)]
    rfl
  · simp [Expr.erase, htargs, hea]

/-- A property starts with a token other than `}`. -/
theorem Property.start (q : Property) :
    ∃ k, q.words.flatten.head? = some k ∧ k ≠ .punct "}" ∧
      ∀ (t : Token) (s : ParseState), t.kind = k → (fun _ => pure () : Token → ParseM Unit) t s = .ok () s := by
  cases q with
  | shorthand sp name => exact ⟨.ident name, by simp [Property.words, identWord], by simp, fun _ _ _ => rfl⟩
  | keyValue sp key value =>
    cases key with
    | ident name =>
      by_cases h : name ∈ Lex.reservedWords
      · exact ⟨.keyword name, by simp [Property.words, PropKey.words, propertyName, h, keywordWord], by simp,
          fun _ _ _ => rfl⟩
      · exact ⟨.ident name, by simp [Property.words, PropKey.words, propertyName, h, identWord], by simp,
          fun _ _ _ => rfl⟩
    | string v => exact ⟨.string v, by simp [Property.words, PropKey.words], by simp, fun _ _ _ => rfl⟩
    | number t => exact ⟨.number t, by simp [Property.words, PropKey.words], by simp, fun _ _ _ => rfl⟩
  | spread sp value => exact ⟨.punct "...", by simp [Property.words, punctWord], by simp, fun _ _ _ => rfl⟩


/-- The steps of `parseProperty` after the key of a key and value, in the
state `s₁` after the key: `hcolon` states that a `:` comes next, `hne` that
a token follows it, and `hp` what `parseAssign` reads. -/
macro "property_tail " s₁:ident hcolon:ident hne:ident hp:ident : tactic => `(tactic| (
  rw [Parse.bind_eq (Parse.pure_eq _ _), Parse.bind_eq (Parse.peek_eq (s := $s₁) rfl)]
  simp only [Token.isPunct, $hcolon:ident, beq_self_eq_true, ↓reduceIte]
  rw [Parse.bind_eq (Parse.discard_eq (Parse.advance_cons (s := $s₁) rfl $hne))]
  rw [Parse.bind_eq $hp, Parse.bind_eq (Parse.spanFrom_eq _ _)]
  rfl))

/-- A property, when `parseAssign` reads the value of a key and value. -/
theorem parseProperty_reads {T : Edition} (g : Nat) (q : Property) (hq : q.wf T = true)
    (hv : ∀ sp key v, q = .keyValue sp key v → ReadsE T (Parse.parseAssign g) v EndsAssign)
    (hsv : ∀ sp v, q = .spread sp v → ReadsE T (Parse.parseAssign g) v EndsAssign) :
    ReadsP T (Parse.parseProperty (g + 1)) q (EndsItem "}") := by
  intro s ts rest hT hs hl ht hn hr hE ha
  cases q with
  | shorthand sp name =>
    have hname : name ∉ Parse.refusedNames := by simpa [Property.wf, exprName] using hq
    obtain ⟨x, ts', rfl, hx, h'⟩ := Touching.cons_one (by simpa [Property.words, identWord] using ht)
    simp [Touching] at h'; subst h'
    obtain ⟨u, r, rfl, hu⟩ := hE
    have hs' : s.rest = x :: u :: r := by simpa using hs
    refine ⟨.shorthand x.span name, past s x (u :: r), ?_, by simp [Property.erase], leaves_advance hs' hl⟩
    rcases hu with hu | hu <;>
      simp [Parse.parseProperty, Parse.advance_eq hs', hx, Parse.peek_eq (s := past s x (u :: r)) rfl,
        Token.isPunct, hu, hname, bind, EStateM.bind, pure, EStateM.pure]
  | keyValue sp key value =>
    have hvr := hv sp key value rfl
    obtain ⟨k, hkw⟩ : ∃ k, key.words = [[k]] := by
      cases key with
      | ident name =>
        exact ⟨if Lex.reservedWords.contains name then .keyword name else .ident name,
          by simp only [PropKey.words, propertyName]; split <;> rfl⟩
      | string v => exact ⟨_, rfl⟩
      | number t => exact ⟨_, rfl⟩
    obtain ⟨x, ts₁, rfl, hx, h₁⟩ := Touching.cons_one (k := k) (by simpa [Property.words, hkw] using ht)
    obtain ⟨colon, vts, rfl, hcolon, hv'⟩ := Touching.cons_one (by simpa [punctWord] using h₁)
    have hs' : s.rest = x :: colon :: (vts ++ rest) := by simpa using hs
    have hne : vts ++ rest ≠ [] := by simp [hr]
    let s₁ := past s x (colon :: (vts ++ rest))
    let s₂ : ParseState := { s₁ with rest := vts ++ rest, left := s₁.left - 1, lastStop := colon.span.stop }
    have hl₂ : s₂.left = s₂.rest.length := by simp [s₂, s₁, hl, hs']
    obtain ⟨v', s₃, hp, he, hL⟩ := hvr s₂ vts rest hT rfl hl₂ hv' (fun y hy => hn y (by simp [List.mem_of_mem_tail hy])) hr
      (endsItem_assign (by simp) hE) (by simpa [Property.afterOK] using ha)
    refine ⟨.keyValue ⟨x.span.start, s₃.lastStop⟩ key v', s₃, ?_, by simp [Property.erase, he], ?_⟩
    · simp only [Parse.parseProperty]
      rw [Parse.bind_eq (Parse.advance_eq hs')]
      cases key with
      | ident name =>
        simp [PropKey.words, propertyName, keywordWord, identWord] at hkw
        by_cases h : name ∈ Lex.reservedWords <;> simp [h] at hkw <;> subst hkw <;>
          rw [if_neg (by simp [Token.isPunct, hx]), Parse.bind_eq (Parse.pure_eq _ _)] <;> simp only [hx] <;>
          property_tail s₁ hcolon hne hp
      | string v =>
        simp [PropKey.words] at hkw; subst hkw
        rw [if_neg (by simp [Token.isPunct, hx]), Parse.bind_eq (Parse.pure_eq _ _)]; simp only [hx]; property_tail s₁ hcolon hne hp
      | number t =>
        simp [PropKey.words] at hkw; subst hkw
        rw [if_neg (by simp [Token.isPunct, hx]), Parse.bind_eq (Parse.pure_eq _ _)]; simp only [hx]; property_tail s₁ hcolon hne hp
    · exact leaves_trans (leaves_advance hs' hl) (leaves_trans (leaves_advance (s := s₁) rfl
        (by simp [s₁, hl, hs'])) hL)
  | spread sp value =>
    -- `...` and then the value, as the value of a key and value.
    have hvr := hsv sp value rfl
    obtain ⟨x, vts, rfl, hx, hv'⟩ := Touching.cons_one (by simpa [Property.words, punctWord] using ht)
    have hs' : s.rest = x :: (vts ++ rest) := by simpa using hs
    let s₁ := past s x (vts ++ rest)
    have hl₁ : s₁.left = s₁.rest.length := by simp [s₁, hl, hs']
    obtain ⟨v', s₂, hp, he, hL⟩ := hvr s₁ vts rest hT rfl hl₁ hv' (fun y hy => hn y (by simp [List.mem_of_mem_tail hy])) hr
      (endsItem_assign (by simp) hE) (by simpa [Property.afterOK] using ha)
    refine ⟨.spread ⟨x.span.start, s₂.lastStop⟩ v', s₂, ?_, by simp [Property.erase, he],
      leaves_trans (leaves_advance hs' hl) hL⟩
    simp only [Parse.parseProperty]
    rw [Parse.bind_eq (Parse.advance_cons hs' (by simp [hr])), if_pos (by simp [Token.isPunct, hx])]
    have hf : T.supports .objectSpread = true := by simp only [Property.wf, Bool.and_eq_true] at hq; exact hq.1
    rw [Parse.bind_eq (Parse.requireFeature_ok (by simpa [hT] using hf))]
    rw [Parse.bind_eq hp, Parse.bind_eq (Parse.spanFrom_eq _ _)]
    rfl


/-- `{ props }`, when `parseProperty` reads each property. -/
theorem parseObjectLiteral_reads {T : Edition} (g : Nat) (sp : Span) (props : List Property)
    (hprops : ∀ q ∈ props, ReadsP T (Parse.parseProperty g) q (EndsItem "}")) :
    ReadsE T (Parse.parseObjectLiteral (g + 1)) (.object sp props) (fun _ => True) := by
  intro s ts rest hT hs hl ht hn hr _ ha
  obtain ⟨lp, its, rp, rfl, hlp, hits, hrp⟩ := Touching.enclosed (by simpa [Expr.words, enclose] using ht)
  have hs₁ : s.rest = lp :: (its ++ rp :: rest) := by simpa using hs
  let s₁ : ParseState := { s with rest := its ++ rp :: rest, left := s.left - 1, lastStop := lp.span.stop }
  have hl₁ : s₁.left = s₁.rest.length := by simp [s₁, hl, hs₁]
  rw [Property.wordsOf_eq] at hits
  obtain ⟨res, s₂, hit, he, hL⟩ := iterate_list (close := "}") (refuse := fun _ => pure ()) (by decide)
    props (10 * (s₁.left + 1)) #[] s₁ its rest rp hprops (fun q _ => Property.start q)
    (by have := length_items hits; have : s₁.left = its.length + rest.length + 1 := by simp [s₁, hl, hs₁]; omega
        omega) hT rfl hrp hl₁ hits
    (fun y hy => hn y (by simp [hy])) (Property.listAfter props (by simpa [Expr.afterOK] using ha))
  have hs₂ : s₂.rest = rp :: rest := hL.rest_eq
  let s₃ : ParseState := { s₂ with rest := rest, left := s₂.left - 1, lastStop := rp.span.stop }
  refine ⟨.object ⟨lp.span.start, s₃.lastStop⟩ res.toList, s₃, ?_, ?_,
    leaves_trans (leaves_advance hs₁ hl) (leaves_trans hL (leaves_advance hs₂ (by rw [hL.left_eq, hs₂])))⟩
  · simp only [Parse.parseObjectLiteral]
    rw [Parse.bind_eq (Parse.expectPunct_ok hs₁ (by simp) hlp), Parse.bind_eq (Parse.budget_eq _)]
    rw [Parse.bind_eq (s' := s₂) (a := res) hit, Parse.bind_eq (Parse.expectPunct_ok hs₂ hr hrp),
      Parse.bind_eq (Parse.spanFrom_eq _ _)]
    rfl
  · simpa [Expr.erase, Property.eraseAll_eq] using he

/-- `parseExpression` reads what `parseAssign` reads, when no `,` follows. -/
theorem expression_reads {T : Edition} (g : Nat) (e : Expr) (h : ReadsE T (Parse.parseAssign g) e EndsAssign) :
    ReadsE T (Parse.parseExpression (g + 1)) e EndsExpr := by
  intro s ts rest hT hs hl ht hn hr hE ha
  obtain ⟨e', s', hp, he, hL⟩ := h s ts rest hT hs hl ht hn hr hE.1 ha
  obtain ⟨u, r, rfl⟩ := List.exists_cons_of_ne_nil hr
  have hu : u.kind ≠ .punct "," := hE.2 u rfl
  refine ⟨e', s', ?_, he, hL⟩
  simp [Parse.parseExpression, bind, EStateM.bind, hp, Parse.peek_eq hL.rest_eq, Token.isPunct, hu, pure,
    EStateM.pure]

theorem refuseArrowLookalike_ok {s : ParseState} {u : Token} {r : List Token} (hs : s.rest = u :: r)
    (hu : u.kind ≠ .punct "{") : Parse.refuseArrowLookalike s = .ok () s := by
  simp [Parse.refuseArrowLookalike, Parse.peek_eq hs, Token.isPunct, hu, bind, EStateM.bind, pure,
    EStateM.pure]

theorem notFirst_cons {k k' : TokenKind} {after : List TokenKind} (h : notFirst k (k' :: after) = true) :
    k' ≠ k := by
  intro e; subst e; simp [notFirst] at h

/-- `( inner )`, when `parseExpression` reads `inner`. -/
theorem parsePrimary_paren {T : Edition} (f : Nat) (sp : Span) (inner : Expr)
    (h : ReadsE T (Parse.parseExpression f) inner EndsExpr) :
    ReadsE T (Parse.parsePrimary (f + 1)) (.paren sp inner) (fun _ => True) := by
  intro s ts rest hT hs hl ht hn hr _ ha
  obtain ⟨lp, its, rp, rfl, hlp, hits, hrp⟩ := Touching.enclosed (by simpa [Expr.words] using ht)
  have hs₁ : s.rest = lp :: (its ++ rp :: rest) := by simpa using hs
  simp only [Expr.afterOK, Bool.and_eq_true] at ha
  obtain ⟨u, r, rfl⟩ := List.exists_cons_of_ne_nil hr
  have hu : u.kind ≠ .punct "{" := notFirst_cons ha.1
  let s₁ : ParseState := { s with rest := its ++ rp :: u :: r, left := s.left - 1, lastStop := lp.span.stop }
  have hl₁ : s₁.left = s₁.rest.length := by simp [s₁, hl, hs₁]
  have hE : EndsExpr (rp :: u :: r) :=
    ⟨endsAssign_separator hrp (by simp [separators]), fun t ht => by
      simp at ht; subst ht; rw [hrp]; exact punct_ne (by decide)⟩
  obtain ⟨inner', s₂, hp, he, hL⟩ := h s₁ its (rp :: u :: r) (hT ▸ rfl) rfl hl₁ hits
    (fun y hy => hn y (by simp [List.mem_of_mem_tail hy])) (by simp) hE (by simpa [hrp] using ha.2)
  have hs₂ : s₂.rest = rp :: u :: r := hL.rest_eq
  let s₃ : ParseState := { s₂ with rest := u :: r, left := s₂.left - 1, lastStop := rp.span.stop }
  refine ⟨.paren ⟨lp.span.start, s₃.lastStop⟩ inner', s₃, ?_, by simp [Expr.erase, he],
    leaves_trans (leaves_advance hs₁ hl) (leaves_trans hL (leaves_advance hs₂ (by rw [hL.left_eq, hs₂])))⟩
  simp only [Parse.parsePrimary]
  rw [Parse.bind_eq (Parse.peek_eq hs₁)]
  simp only [hlp]
  rw [Parse.bind_eq (Parse.discard_eq (Parse.advance_cons hs₁ (by simp)))]
  rw [Parse.bind_eq (s' := s₂) hp, Parse.bind_eq (Parse.expectPunct_ok hs₂ (by simp) hrp),
    Parse.bind_eq (refuseArrowLookalike_ok (s := s₃) rfl hu), Parse.bind_eq (Parse.spanFrom_eq _ _)]
  rfl

/-! ### Left-hand sides -/

/-- The expression that a chain of members, indices and calls starts with. -/
def lhsHead : Expr → Expr
  | .member _ o _ | .optMember _ o _ | .index _ o _ | .call _ o _ => lhsHead o
  | e => e

/-- The words of the members, indices and calls of a chain, after its head. -/
def lhsSuffix : Expr → List Word
  | .member _ o n => lhsSuffix o ++ [punctWord ".", propertyName n]
  | .optMember _ o n => lhsSuffix o ++ [punctWord "?.", propertyName n]
  | .index _ o i => lhsSuffix o ++ punctWord "[" :: i.words ++ [punctWord "]"]
  | .call _ o as => lhsSuffix o ++ callBreak o ++ enclose "(" ")" (Expr.wordsOf as)
  | _ => []

/-- The number of members, indices and calls of a chain. -/
def lhsSteps : Expr → Nat
  | .member _ o _ | .optMember _ o _ | .index _ o _ | .call _ o _ => lhsSteps o + 1
  | _ => 0

theorem words_lhs (e : Expr) : e.words = (lhsHead e).words ++ lhsSuffix e := by
  cases e with
  | member _ o n => simp [lhsHead, lhsSuffix, Expr.words, words_lhs o]
  | optMember _ o n => simp [lhsHead, lhsSuffix, Expr.words, words_lhs o]
  | index _ o i => simp [lhsHead, lhsSuffix, Expr.words, words_lhs o]
  | call _ o as => simp [lhsHead, lhsSuffix, Expr.words, words_lhs o]
  | _ => simp [lhsHead, lhsSuffix]

theorem wf_lhsHead {T : Edition} (e : Expr) (h : e.wfAt T .lhs = true) : (lhsHead e).wfAt T .primary = true := by
  cases e with
  | member _ o n => simp [Expr.wfAt] at h; simpa [lhsHead] using wf_lhsHead o h
  | optMember _ o n => simp [Expr.wfAt] at h; simpa [lhsHead] using wf_lhsHead o h.2
  | index _ o i => simp [Expr.wfAt] at h; simpa [lhsHead] using wf_lhsHead o h.1
  | call _ o as => simp [Expr.wfAt] at h; simpa [lhsHead] using wf_lhsHead o h.1
  | _ => simp_all [lhsHead, Expr.wfAt]

theorem afterOK_lhsHead (e : Expr) (after : List TokenKind) (h : e.afterOK after = true) :
    (lhsHead e).afterOK ((lhsSuffix e).flatten ++ after) = true := by
  cases e with
  | member _ o n =>
    simp [Expr.afterOK] at h
    simpa [lhsHead, lhsSuffix, punctWord] using afterOK_lhsHead o _ h
  | optMember _ o n =>
    simp [Expr.afterOK] at h
    simpa [lhsHead, lhsSuffix, punctWord] using afterOK_lhsHead o _ h
  | index _ o i =>
    simp [Expr.afterOK] at h
    simpa [lhsHead, lhsSuffix, punctWord, Expr.tokens] using afterOK_lhsHead o _ h.1
  | call _ o as =>
    simp only [Expr.afterOK, Bool.and_eq_true] at h
    obtain ⟨h, _⟩ := h
    simpa [lhsHead, lhsSuffix] using afterOK_lhsHead o _ h
  | _ => simpa [lhsHead, lhsSuffix] using h

theorem height_lhsHead (e : Expr) : (lhsHead e).height ≤ e.height := by
  cases e with
  | member _ o n => have := height_lhsHead o; simp [lhsHead, Expr.height]; omega
  | optMember _ o n => have := height_lhsHead o; simp [lhsHead, Expr.height]; omega
  | index _ o i => have := height_lhsHead o; simp [lhsHead, Expr.height]; omega
  | call _ o as => have := height_lhsHead o; simp [lhsHead, Expr.height]; omega
  | _ => simp [lhsHead]

theorem length_propertyName (n : String) : (propertyName n).length = 1 := by
  unfold propertyName; split <;> rfl

theorem lhsSteps_le (e : Expr) : lhsSteps e ≤ (lhsSuffix e).flatten.length := by
  cases e with
  | member _ o n => have := lhsSteps_le o; simp [lhsSteps, lhsSuffix, punctWord, length_propertyName] at this ⊢; omega
  | optMember _ o n => have := lhsSteps_le o; simp [lhsSteps, lhsSuffix, punctWord, length_propertyName] at this ⊢; omega
  | index _ o i => have := lhsSteps_le o; simp [lhsSteps, lhsSuffix, punctWord] at this ⊢; omega
  | call _ o as => have := lhsSteps_le o; simp [lhsSteps, lhsSuffix, enclose, punctWord] at this ⊢; omega
  | _ => simp [lhsSteps]


/-! ### Steps of the left-hand side loop -/

theorem refuseSplitMember_ok {s : ParseState} {x : Token} {r : List Token} (hs : s.rest = x :: r)
    (hx : x.newlineBefore = false) : Parse.refuseSplitMember s = .ok () s := by
  simp [Parse.refuseSplitMember, Parse.peek_eq hs, Parse.peekAt_rest, hs, hx, bind, EStateM.bind, pure,
    EStateM.pure]

theorem readPropertyName_ok {s : ParseState} {x u : Token} {r : List Token} {name : String}
    (hs : s.rest = x :: u :: r) (hx : [x.kind] = propertyName name) :
    Parse.readPropertyName s = .ok name (past s x (u :: r)) := by
  unfold propertyName at hx
  split at hx <;> simp [keywordWord, identWord] at hx <;>
    simp [Parse.readPropertyName, Parse.advance_eq hs, hx, bind, EStateM.bind, pure, EStateM.pure]

/-- A `.` and a property name. -/
theorem lhsStep_member {pi : ParseM Expr} {pa : ParseM (List Expr)} {start : Pos} {acc : Expr}
    {s : ParseState} {dot nm u : Token} {r : List Token} {name : String}
    (hs : s.rest = dot :: nm :: u :: r) (hl : s.left = s.rest.length) (hdot : dot.kind = .punct ".")
    (hnm : [nm.kind] = propertyName name) (hn : nm.newlineBefore = false) :
    ∃ sp s', Parse.leftHandSideStep pi pa start acc s = .ok (.member sp acc name, true) s' ∧
      Leaves s s' (u :: r) := by
  let s₁ : ParseState := { s with rest := nm :: u :: r, left := s.left - 1, lastStop := dot.span.stop }
  have hl₁ : s₁.left = s₁.rest.length := by simp [s₁, hl, hs]
  refine ⟨⟨start, nm.span.stop⟩, past s₁ nm (u :: r), ?_,
    leaves_trans (leaves_advance hs hl) (leaves_advance (s := s₁) rfl hl₁)⟩
  simp only [Parse.leftHandSideStep]
  rw [Parse.bind_eq (Parse.peek_eq hs)]
  simp only [Token.isPunct, hdot, beq_self_eq_true, ↓reduceIte]
  rw [Parse.bind_eq (Parse.discard_eq (Parse.advance_eq hs))]
  rw [Parse.bind_eq (refuseSplitMember_ok (s := s₁) rfl hn), Parse.bind_eq (readPropertyName_ok (s := s₁) rfl hnm),
    Parse.bind_eq (Parse.spanFrom_eq _ _)]
  rfl

/-- A `?.` and a property name, when the target has optional chaining. -/
theorem lhsStep_optMember {pi : ParseM Expr} {pa : ParseM (List Expr)} {start : Pos} {acc : Expr}
    {s : ParseState} {dot nm u : Token} {r : List Token} {name : String}
    (hs : s.rest = dot :: nm :: u :: r) (hl : s.left = s.rest.length) (hdot : dot.kind = .punct "?.")
    (hnm : [nm.kind] = propertyName name) (hn : nm.newlineBefore = false)
    (hT : s.target.supports .optionalChaining = true) :
    ∃ sp s', Parse.leftHandSideStep pi pa start acc s = .ok (.optMember sp acc name, true) s' ∧
      Leaves s s' (u :: r) := by
  let s₁ : ParseState := { s with rest := nm :: u :: r, left := s.left - 1, lastStop := dot.span.stop }
  have hl₁ : s₁.left = s₁.rest.length := by simp [s₁, hl, hs]
  refine ⟨⟨start, nm.span.stop⟩, past s₁ nm (u :: r), ?_,
    leaves_trans (leaves_advance hs hl) (leaves_advance (s := s₁) rfl hl₁)⟩
  simp only [Parse.leftHandSideStep]
  rw [Parse.bind_eq (Parse.peek_eq hs)]
  simp (config := { decide := true }) only [Token.isPunct, hdot, beq_self_eq_true, ↓reduceIte, beq_iff_eq,
    TokenKind.punct.injEq]
  have hreq : Parse.requireFeature dot .optionalChaining s = .ok () s := by
    simp [Parse.requireFeature, hT, get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind, pure,
      EStateM.pure]
  rw [Parse.bind_eq hreq, Parse.bind_eq (Parse.discard_eq (Parse.advance_eq hs))]
  rw [Parse.bind_eq (refuseSplitMember_ok (s := s₁) rfl hn), Parse.bind_eq (readPropertyName_ok (s := s₁) rfl hnm),
    Parse.bind_eq (Parse.spanFrom_eq _ _)]
  rfl

/-- A `[`, an index that `pi` reads, and a `]`. -/
theorem lhsStep_index {pi : ParseM Expr} {pa : ParseM (List Expr)} {start : Pos} {acc : Expr}
    {s s₂ : ParseState} {lb rb : Token} {its r : List Token} {i' : Expr}
    (hs : s.rest = lb :: (its ++ rb :: r)) (hlb : lb.kind = .punct "[") (hr : r ≠ [])
    (hi : pi { s with rest := its ++ rb :: r, left := s.left - 1, lastStop := lb.span.stop } = .ok i' s₂)
    (hs₂ : s₂.rest = rb :: r) (hrb : rb.kind = .punct "]") :
    Parse.leftHandSideStep pi pa start acc s =
      .ok (.index ⟨start, rb.span.stop⟩ acc i', true)
        { s₂ with rest := r, left := s₂.left - 1, lastStop := rb.span.stop } := by
  simp only [Parse.leftHandSideStep]
  rw [Parse.bind_eq (Parse.peek_eq hs)]
  simp (config := { decide := true }) only [Token.isPunct, hlb, beq_self_eq_true, ↓reduceIte, beq_iff_eq,
    TokenKind.punct.injEq]
  rw [Parse.bind_eq (Parse.discard_eq (Parse.advance_cons hs (by simp))), Parse.bind_eq hi,
    Parse.bind_eq (Parse.expectPunct_ok hs₂ hr hrb), Parse.bind_eq (Parse.spanFrom_eq _ _)]
  rfl

/-- The arguments of a call, which `pa` reads. -/
theorem lhsStep_call {pi : ParseM Expr} {pa : ParseM (List Expr)} {start : Pos} {acc : Expr}
    {s s₂ : ParseState} {lp : Token} {r : List Token} {args' : List Expr}
    (hs : s.rest = lp :: r) (hlp : lp.kind = .punct "(") (ha : pa s = .ok args' s₂)
    (hasync : ∀ sp, acc = .ident sp "async" → lp.newlineBefore = true) :
    Parse.leftHandSideStep pi pa start acc s = .ok (.call ⟨start, s₂.lastStop⟩ acc args', true) s₂ := by
  simp only [Parse.leftHandSideStep]
  rw [Parse.bind_eq (Parse.peek_eq hs)]
  simp (config := { decide := true }) only [Token.isPunct, hlp, beq_self_eq_true, ↓reduceIte, beq_iff_eq,
    TokenKind.punct.injEq]
  rw [Parse.bind_eq ha]
  cases acc with
  | ident sp name =>
    by_cases hn : name = "async"
    · subst hn
      simp [hasync sp rfl, Parse.spanFrom_eq, bind, EStateM.bind, pure, EStateM.pure]
    · simp [hn, Parse.spanFrom_eq, bind, EStateM.bind, pure, EStateM.pure]
  | _ => simp [Parse.spanFrom_eq, bind, EStateM.bind, pure, EStateM.pure]

/-- The loop stops before a token that continues no left-hand side. -/
theorem lhsStep_stop {pi : ParseM Expr} {pa : ParseM (List Expr)} {start : Pos} {acc : Expr}
    {s : ParseState} {u : Token} {r : List Token} (hs : s.rest = u :: r) (hu : EndsLhs (u :: r)) :
    Parse.leftHandSideStep pi pa start acc s = .ok (acc, false) s := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hu u rfl
  by_cases h : u.kind = .punct "!"
  · have := h5 h
    simp [Parse.leftHandSideStep, Parse.peek_eq hs, Token.isPunct, h, this, bind, EStateM.bind,
      pure, EStateM.pure]
  · simp [Parse.leftHandSideStep, Parse.peek_eq hs, Token.isPunct, h1, h2, h3, h4, h, bind, EStateM.bind,
      pure, EStateM.pure]


/-- `pa` reads `( args )` as `args`, apart from spans. -/
def ArgsRead (T : Edition) (pa : ParseM (List Expr)) (args : List Expr) : Prop :=
  ∀ (s : ParseState) (ts rest : List Token), s.target = T → s.rest = ts ++ rest →
    s.left = s.rest.length → Touching ts (enclose "(" ")" (Expr.wordsOf args)) →
    (∀ y ∈ ts, NoBreak y) → rest ≠ [] →
    Expr.afterOKList (.punct ")" :: rest.map (·.kind)) args = true →
    ∃ args' s', pa s = .ok args' s' ∧ Expr.eraseAll args' = Expr.eraseAll args ∧ Leaves s s' rest

/-- A property name after `.` is one token. -/
theorem Touching.propertyName {ts : List Token} {name : String} (h : Touching ts [propertyName name]) :
    ∃ nm, ts = [nm] ∧ [nm.kind] = propertyName name := by
  obtain ⟨a, b, rfl, ha, _, hb⟩ := h
  simp [Touching] at hb; subst hb
  have hlen := congrArg List.length ha
  rw [List.length_map, length_propertyName] at hlen
  match a, ha with
  | [nm], ha => exact ⟨nm, by simp, by simpa using ha⟩

/-- A property name is not a `(`. -/
theorem propertyName_ne_paren {nm : Token} {name : String} (h : [nm.kind] = propertyName name) :
    nm.kind ≠ .punct "(" := by
  unfold propertyName at h
  split at h <;> simp [keywordWord, identWord] at h <;> simp [h]

/-- The loop of `parseLeftHandSide` reads the members, indices and calls of a
chain after its head, and goes on with what follows them. -/
theorem lhs_loop {T : Edition} {pi : ParseM Expr} {pa : ParseM (List Expr)} {start : Pos} {H : Nat}
    (hE : ∀ x : Expr, x.height < H → x.wfAt T .assign = true → ReadsE T pi x EndsExpr)
    (hA : ∀ args : List Expr, Expr.heightOf args < H → Expr.allWF T args = true → ArgsRead T pa args) :
    ∀ (e : Expr), e.wfAt T .lhs = true → e.height ≤ H →
      ∀ (n : Nat) (acc : Expr) (s : ParseState) (ts rest : List Token),
      acc.erase = (lhsHead e).erase → s.target = T → s.rest = ts ++ rest → s.left = s.rest.length →
      Touching ts (lhsSuffix e) → (∀ y ∈ ts, NoBreak y) → rest ≠ [] →
      e.afterOK (rest.map (·.kind)) = true →
      ∃ e' s', Parse.iterate (n + lhsSteps e) acc (Parse.leftHandSideStep pi pa start) s =
        Parse.iterate n e' (Parse.leftHandSideStep pi pa start) s' ∧ e'.erase = e.erase ∧ Leaves s s' rest := by
  intro e he hH n acc s ts rest hacc hT hs hl ht hn hr ha
  cases e with
  | member sp o name =>
    simp only [Expr.wfAt] at he
    have hHo : o.height ≤ H := by simp [Expr.height] at hH; omega
    simp only [lhsSuffix] at ht
    obtain ⟨ots, more, rfl, hot, hmore⟩ := Touching.append_split ht
    obtain ⟨dot, more₁, rfl, hdot, hm₁⟩ := Touching.cons_one (by simpa [punctWord] using hmore)
    obtain ⟨nm, rfl, hnm⟩ := Touching.propertyName hm₁
    simp only [Expr.afterOK] at ha
    obtain ⟨o', s₁, hit, he', hL⟩ := lhs_loop hE hA o he hHo (n + 1) acc s ots (dot :: nm :: rest)
      (by simpa [lhsHead] using hacc) hT (by simp [hs]) hl hot (fun y hy => hn y (by simp [hy])) (by simp)
      (by simpa [hdot, ← hnm] using ha)
    obtain ⟨u, r, rfl⟩ := List.exists_cons_of_ne_nil hr
    have hs₁ : s₁.rest = dot :: nm :: u :: r := hL.rest_eq
    have hl₁ : s₁.left = s₁.rest.length := by rw [hL.left_eq, hL.rest_eq]
    obtain ⟨sp', s₂, hstep, hL₂⟩ := lhsStep_member (pi := pi) (pa := pa) (start := start) (acc := o') hs₁ hl₁
      hdot hnm (hn nm (by simp) (propertyName_ne_paren hnm))
    refine ⟨.member sp' o' name, s₂, ?_, by simp [Expr.erase, he'], leaves_trans hL hL₂⟩
    rw [show n + lhsSteps (.member sp o name) = (n + 1) + lhsSteps o by simp [lhsSteps]; omega, hit,
      Parse.iterate_true hstep]
  | optMember sp o name =>
    simp only [Expr.wfAt, Bool.and_eq_true] at he
    have hHo : o.height ≤ H := by simp [Expr.height] at hH; omega
    simp only [lhsSuffix] at ht
    obtain ⟨ots, more, rfl, hot, hmore⟩ := Touching.append_split ht
    obtain ⟨dot, more₁, rfl, hdot, hm₁⟩ := Touching.cons_one (by simpa [punctWord] using hmore)
    obtain ⟨nm, rfl, hnm⟩ := Touching.propertyName hm₁
    simp only [Expr.afterOK] at ha
    obtain ⟨o', s₁, hit, he', hL⟩ := lhs_loop hE hA o he.2 hHo (n + 1) acc s ots (dot :: nm :: rest)
      (by simpa [lhsHead] using hacc) hT (by simp [hs]) hl hot (fun y hy => hn y (by simp [hy])) (by simp)
      (by simpa [hdot, ← hnm] using ha)
    obtain ⟨u, r, rfl⟩ := List.exists_cons_of_ne_nil hr
    have hs₁ : s₁.rest = dot :: nm :: u :: r := hL.rest_eq
    have hl₁ : s₁.left = s₁.rest.length := by rw [hL.left_eq, hL.rest_eq]
    obtain ⟨sp', s₂, hstep, hL₂⟩ := lhsStep_optMember (pi := pi) (pa := pa) (start := start) (acc := o') hs₁ hl₁
      hdot hnm (hn nm (by simp) (propertyName_ne_paren hnm)) (by rw [hL.target_eq, hT]; exact he.1)
    refine ⟨.optMember sp' o' name, s₂, ?_, by simp [Expr.erase, he'], leaves_trans hL hL₂⟩
    rw [show n + lhsSteps (.optMember sp o name) = (n + 1) + lhsSteps o by simp [lhsSteps]; omega, hit,
      Parse.iterate_true hstep]
  | index sp o i =>
    simp only [Expr.wfAt, Bool.and_eq_true] at he
    have hHo : o.height ≤ H := by simp [Expr.height] at hH; omega
    have hHi : i.height < H := by simp [Expr.height] at hH; omega
    simp only [lhsSuffix] at ht
    rw [List.append_assoc] at ht
    obtain ⟨ots, more, rfl, hot, hmore⟩ := Touching.append_split ht
    obtain ⟨lb, its, rb, rfl, hlb, hits, hrb⟩ := Touching.enclosed hmore
    simp only [Expr.afterOK, Bool.and_eq_true] at ha
    obtain ⟨o', s₁, hit, he', hL⟩ := lhs_loop hE hA o he.1 hHo (n + 1) acc s ots (lb :: (its ++ rb :: rest))
      (by simpa [lhsHead] using hacc) hT (by simp [hs]) hl hot (fun y hy => hn y (by simp [hy])) (by simp)
      (by simpa [hlb, hrb, hits.kinds, Expr.tokens] using ha.1)
    have hs₁ : s₁.rest = lb :: (its ++ rb :: rest) := hL.rest_eq
    have hl₁ : s₁.left = s₁.rest.length := by rw [hL.left_eq, hL.rest_eq]
    let s₁' : ParseState := { s₁ with rest := its ++ rb :: rest, left := s₁.left - 1, lastStop := lb.span.stop }
    have hE' : EndsExpr (rb :: rest) :=
      ⟨endsAssign_separator hrb (by simp [separators]), fun t ht => by
        simp at ht; subst ht; rw [hrb]; exact punct_ne (by decide)⟩
    obtain ⟨i', s₂, hpi, hei, hLi⟩ := hE i hHi he.2 s₁' its (rb :: rest) (hL.target_eq.trans hT) rfl
      (by simp [s₁', hl₁, hs₁]) hits (fun y hy => hn y (by simp [List.mem_of_mem_tail hy])) (by simp) hE' (by simpa [hrb] using ha.2)
    have hs₂ : s₂.rest = rb :: rest := hLi.rest_eq
    refine ⟨.index ⟨start, rb.span.stop⟩ o' i', { s₂ with rest := rest, left := s₂.left - 1, lastStop := rb.span.stop },
      ?_, by simp [Expr.erase, he', hei], ?_⟩
    · rw [show n + lhsSteps (.index sp o i) = (n + 1) + lhsSteps o by simp [lhsSteps]; omega, hit,
        Parse.iterate_true (lhsStep_index hs₁ hlb hr hpi hs₂ hrb)]
    · exact leaves_trans hL (leaves_trans (leaves_advance hs₁ hl₁)
        (leaves_trans hLi (leaves_advance hs₂ (by rw [hLi.left_eq, hs₂]))))
  | call sp o args =>
    simp only [Expr.wfAt, Bool.and_eq_true] at he
    have hHo : o.height ≤ H := by simp [Expr.height] at hH; omega
    have hHa : Expr.heightOf args < H := by simp [Expr.height] at hH; omega
    simp only [lhsSuffix] at ht
    rw [List.append_assoc] at ht
    obtain ⟨ots, ats, rfl, hot, hbats⟩ := Touching.append_split ht
    obtain ⟨hbreak, hats⟩ := Touching.after_callBreak hbats
    obtain ⟨lp, its, rp, rfl, hlp, _, _⟩ := Touching.enclosed (by simpa [enclose] using hats)
    simp only [Expr.afterOK, Bool.and_eq_true] at ha
    obtain ⟨hao, hargs⟩ := ha
    obtain ⟨o', s₁, hit, he', hL⟩ := lhs_loop hE hA o he.1 hHo (n + 1) acc s ots (lp :: (its ++ [rp]) ++ rest)
      (by simpa [lhsHead] using hacc) hT (by simp [hs]) hl hot (fun y hy => hn y (by simp [hy])) (by simp)
      (by rw [List.map_append, hats.kinds]; exact hao)
    have hs₁ : s₁.rest = lp :: (its ++ [rp] ++ rest) := by simpa using hL.rest_eq
    have hl₁ : s₁.left = s₁.rest.length := by rw [hL.left_eq, hL.rest_eq]
    obtain ⟨args', s₂, hpa, hea, hLa⟩ := hA args hHa he.2 s₁ (lp :: (its ++ [rp])) rest (hL.target_eq.trans hT)
      hL.rest_eq hl₁ hats (fun y hy => hn y (by simp [hy])) hr hargs
    have hasync : ∀ sp', o' = .ident sp' "async" → lp.newlineBefore = true := by
      intro sp' ho'
      subst ho'
      obtain ⟨sp₀, rfl⟩ : ∃ sp₀, o = .ident sp₀ "async" := by
        cases o <;> simp [Expr.erase] at he'
        exact ⟨_, by rw [he']⟩
      exact hbreak sp₀ rfl lp (by simp)
    refine ⟨.call ⟨start, s₂.lastStop⟩ o' args', s₂, ?_, by simp [Expr.erase, he', hea], leaves_trans hL hLa⟩
    rw [show n + lhsSteps (.call sp o args) = (n + 1) + lhsSteps o by simp [lhsSteps]; omega, hit,
      Parse.iterate_true (lhsStep_call hs₁ hlp hpa hasync)]
  | _ =>
    simp [lhsSuffix, Touching] at ht; subst ht
    exact ⟨acc, s, by simp [lhsSteps], by simpa [lhsHead] using hacc,
      Leaves.refl (by simpa using hs) (by simp [hl, hs])⟩


/-- The first token of an expression. -/
theorem Touching.head {ts : List Token} {e : Expr} (h : Touching ts e.words) :
    ∃ x ts', ts = x :: ts' ∧ startsExpr x.kind = true := by
  obtain ⟨k, hk, hs⟩ := Expr.first e
  have hk' : (ts.map (·.kind)).head? = some k := by rw [h.kinds]; exact hk
  cases ts with
  | nil => simp at hk'
  | cons x ts' => simp at hk'; exact ⟨x, ts', rfl, hk' ▸ hs⟩

/-- A chain of members, indices and calls. -/
theorem parseLeftHandSide_reads {T : Edition} (f : Nat) (e : Expr) (he : e.wfAt T .lhs = true)
    (hP : ReadsE T (Parse.parsePrimary f) (lhsHead e) (fun _ => True))
    (hE : ∀ x : Expr, x.height < e.height → x.wfAt T .assign = true →
      ReadsE T (Parse.parseExpression f) x EndsExpr)
    (hA : ∀ args : List Expr, Expr.heightOf args < e.height → Expr.allWF T args = true →
      ArgsRead T (Parse.parseArguments f) args) :
    ReadsE T (Parse.parseLeftHandSide (f + 1)) e EndsLhs := by
  intro s ts rest hT hs hl ht hn hr hends ha
  rw [words_lhs] at ht
  obtain ⟨hts, sts, rfl, hht, hst⟩ := Touching.append_split ht
  obtain ⟨x, hts', rfl, _⟩ := Touching.head hht
  have hs' : s.rest = x :: (hts' ++ sts ++ rest) := by simpa using hs
  obtain ⟨h', s₁, hp, heh, hL⟩ := hP s (x :: hts') (sts ++ rest) hT (by simp [hs]) hl hht
    (fun y hy => hn y (List.mem_append_left _ hy)) (by simp [hr]) trivial
    (by rw [List.map_append, hst.kinds]; exact afterOK_lhsHead e _ ha)
  have hl₁ : s₁.left = s₁.rest.length := by rw [hL.left_eq, hL.rest_eq]
  obtain ⟨u, r, rfl⟩ := List.exists_cons_of_ne_nil hr
  have hsteps : lhsSteps e ≤ sts.length := by
    have h1 := lhsSteps_le e
    have h2 : sts.length = (lhsSuffix e).flatten.length := by rw [← hst.kinds, List.length_map]
    omega
  obtain ⟨k, hk⟩ : ∃ k, 10 * (s.left + 1) = (k + 1) + lhsSteps e :=
    ⟨10 * (s.left + 1) - 1 - lhsSteps e, by rw [hl, hs']; simp; omega⟩
  obtain ⟨e', s₂, hit, he', hL₂⟩ := lhs_loop (pi := Parse.parseExpression f) (pa := Parse.parseArguments f)
    (start := x.span.start) (H := e.height) hE hA e he (Nat.le_refl _) (k + 1) h' s₁ sts (u :: r) heh
    (hL.target_eq.trans hT) hL.rest_eq hl₁ hst (fun y hy => hn y (List.mem_append_right _ hy)) (by simp) ha
  refine ⟨e', s₂, ?_, he', leaves_trans hL hL₂⟩
  simp only [Parse.parseLeftHandSide]
  rw [Parse.bind_eq (Parse.peek_eq hs'), Parse.bind_eq (Parse.budget_eq _), Parse.bind_eq hp, hk, hit,
    Parse.iterate_false (lhsStep_stop hL₂.rest_eq hends)]

/-! ### Postfix and unary operators -/

theorem Expr.isSimpleTarget_erase : ∀ e : Expr, e.erase.isSimpleTarget = e.isSimpleTarget
  | .paren _ i => by simp [Expr.erase, Expr.isSimpleTarget, Expr.isSimpleTarget_erase i]
  | .ident .. | .member .. | .index .. => by simp [Expr.erase, Expr.isSimpleTarget]
  | .number .. | .bigint .. | .string .. | .bool .. | .null _ | .array .. | .object .. | .call .. | .optMember ..
  | .unary .. | .prefix .. | .postfix .. | .binary .. | .cond .. | .assign .. | .arrow .. | .asConst ..
  | .satisfies .. | .new .. | .spread .. => by
    simp [Expr.erase, Expr.isSimpleTarget]

theorem isSimpleTarget_of_erase {e e' : Expr} (h : e'.erase = e.erase) : e'.isSimpleTarget = e.isSimpleTarget := by
  rw [← Expr.isSimpleTarget_erase e', h, Expr.isSimpleTarget_erase]

theorem updateOp_symbol {t : Token} {op : UpdateOp} (h : t.kind = .punct op.symbol) :
    Parse.updateOp? t = some op := by
  cases op <;> simp [Parse.updateOp?, Token.isPunct, h, UpdateOp.symbol]

/-- A token that can start a primary expression. -/
def startsPrimary : TokenKind → Bool
  | .ident _ | .number _ | .bigint _ | .string _ => true
  | .keyword w => w == "true" || w == "false" || w == "null" || w == "new"
  | .punct p => p == "(" || p == "[" || p == "{"
  | .eof => false

theorem Expr.firstPrimary {T : Edition} (e : Expr) (h : e.wfAt T .primary = true) :
    ∃ k, e.tokens.head? = some k ∧ startsPrimary k = true := by
  cases e <;> simp [Expr.wfAt] at h <;>
    simp [Expr.tokens, Expr.words, identWord, keywordWord, punctWord, enclose, startsPrimary]

theorem tokens_lhs (e : Expr) : e.tokens = (lhsHead e).tokens ++ (lhsSuffix e).flatten := by
  simp [Expr.tokens]
  conv => lhs; rw [words_lhs]
  simp

theorem head_append_of {a b : List TokenKind} {k : TokenKind} (h : a.head? = some k) : (a ++ b).head? = some k := by
  cases a with
  | nil => simp at h
  | cons x a => simpa using h

theorem Expr.firstLhs {T : Edition} (e : Expr) (h : e.wfAt T .lhs = true) :
    ∃ k, e.tokens.head? = some k ∧ startsPrimary k = true := by
  obtain ⟨k, hk, hs⟩ := Expr.firstPrimary (lhsHead e) (wf_lhsHead e h)
  exact ⟨k, by rw [tokens_lhs]; exact head_append_of hk, hs⟩

theorem wfAt_postfix_eq {T : Edition} {e : Expr} (h : ∀ sp op arg, e ≠ .postfix sp op arg) :
    e.wfAt T .postfix = e.wfAt T .lhs := by
  cases e <;> simp_all [Expr.wfAt]

theorem wfAt_unary_eq {T : Edition} {e : Expr} (h₁ : ∀ sp op arg, e ≠ .unary sp op arg)
    (h₂ : ∀ sp op arg, e ≠ .prefix sp op arg) : e.wfAt T .unary = e.wfAt T .postfix := by
  cases e <;> simp_all [Expr.wfAt]

theorem Expr.firstPostfix {T : Edition} (e : Expr) (h : e.wfAt T .postfix = true) :
    ∃ k, e.tokens.head? = some k ∧ startsPrimary k = true := by
  by_cases hp : ∃ sp op arg, e = .postfix sp op arg
  · obtain ⟨sp, op, arg, rfl⟩ := hp
    simp only [Expr.wfAt, Bool.and_eq_true] at h
    obtain ⟨k, hk, hs⟩ := Expr.firstLhs arg h.1
    exact ⟨k, by simp only [Expr.tokens, Expr.words, List.flatten_append]; exact head_append_of hk, hs⟩
  · exact Expr.firstLhs e (by rw [← wfAt_postfix_eq (fun sp op arg h' => hp ⟨sp, op, arg, h'⟩)]; exact h)

theorem unaryOp_none {t : Token} (h : startsPrimary t.kind = true) : Parse.unaryOp? t = none := by
  unfold Parse.unaryOp?; split <;> simp_all [startsPrimary]

theorem updateOp_none {t : Token} (h : startsPrimary t.kind = true) : Parse.updateOp? t = none := by
  have h1 : t.kind ≠ .punct "++" := fun e => by rw [e] at h; simp [startsPrimary] at h
  have h2 : t.kind ≠ .punct "--" := fun e => by rw [e] at h; simp [startsPrimary] at h
  simp [Parse.updateOp?, Token.isPunct, h1, h2]

theorem unaryOp_symbol (op : UnaryOp) : ∃ k, symbol op.symbol = [k] ∧ ∀ t : Token, t.kind = k →
    Parse.unaryOp? t = some op := by
  cases op
  · exact ⟨.punct "!", by simp [symbol, UnaryOp.symbol, Lex.reservedWords, punctWord],
      fun t h => by simp [Parse.unaryOp?, h]⟩
  · exact ⟨.punct "-", by simp [symbol, UnaryOp.symbol, Lex.reservedWords, punctWord],
      fun t h => by simp [Parse.unaryOp?, h]⟩
  · exact ⟨.punct "+", by simp [symbol, UnaryOp.symbol, Lex.reservedWords, punctWord],
      fun t h => by simp [Parse.unaryOp?, h]⟩
  · exact ⟨.punct "~", by simp [symbol, UnaryOp.symbol, Lex.reservedWords, punctWord],
      fun t h => by simp [Parse.unaryOp?, h]⟩
  · exact ⟨.keyword "typeof", by simp [symbol, UnaryOp.symbol, Lex.reservedWords, keywordWord],
      fun t h => by simp [Parse.unaryOp?, h]⟩
  · exact ⟨.keyword "void", by simp [symbol, UnaryOp.symbol, Lex.reservedWords, keywordWord],
      fun t h => by simp [Parse.unaryOp?, h]⟩

/-- A postfix `++` or `--`, or what `parseLeftHandSide` reads. -/
theorem parsePostfix_reads {T : Edition} (f : Nat) (e : Expr) (he : e.wfAt T .postfix = true)
    (hL : ∀ x : Expr, x.height ≤ e.height → x.wfAt T .lhs = true →
      ReadsE T (Parse.parseLeftHandSide f) x EndsLhs) :
    ReadsE T (Parse.parsePostfix (f + 1)) e EndsPostfix := by
  intro s ts rest hT hs hl ht hn hr hends ha
  obtain ⟨x, ts', rfl, _⟩ := Touching.head ht
  have hs' : s.rest = x :: (ts' ++ rest) := by simpa using hs
  by_cases hp : ∃ sp op arg, e = .postfix sp op arg
  · obtain ⟨sp, op, arg, rfl⟩ := hp
    simp only [Expr.wfAt, Bool.and_eq_true] at he
    obtain ⟨ats, ots, hsplit, hat, hot⟩ := Touching.append_split (by simpa [Expr.words] using ht)
    obtain ⟨o, ots', rfl, hok, hot'⟩ := Touching.cons_one (by simpa [punctWord] using hot)
    simp [Touching] at hot'; subst hot'
    have hs₀ : s.rest = ats ++ o :: rest := by rw [hs, hsplit]; simp
    have hne : ats ≠ [] := by obtain ⟨_, _, rfl, _⟩ := Touching.head hat; simp
    have hno : o.newlineBefore = false :=
      noBreak_of hok (by cases op <;> decide) (hn o (tail_sub hsplit hne (.inr (by simp))))
    have hEnd : EndsLhs (o :: rest) := fun t ht => by
      simp at ht; subst ht; rw [hok]; cases op <;> simp [UpdateOp.symbol]
    obtain ⟨arg', s₁, hpa, hea, hL₁⟩ := hL arg (by simp [Expr.height]) he.1 s ats (o :: rest) hT hs₀ hl hat
      (fun y hy => hn y (tail_sub hsplit hne (.inl hy))) (by simp) hEnd (by simpa [Expr.afterOK, hok] using ha)
    have hs₁ : s₁.rest = o :: rest := hL₁.rest_eq
    have hl₁ : s₁.left = s₁.rest.length := by rw [hL₁.left_eq, hL₁.rest_eq]
    have hsim : arg'.isSimpleTarget = true := by rw [isSimpleTarget_of_erase hea]; exact he.2
    refine ⟨.postfix ⟨x.span.start, o.span.stop⟩ op arg',
      { s₁ with rest := rest, left := s₁.left - 1, lastStop := o.span.stop }, ?_, by simp [Expr.erase, hea],
      leaves_trans hL₁ (leaves_advance hs₁ hl₁)⟩
    simp only [Parse.parsePostfix]
    rw [Parse.bind_eq (Parse.peek_eq hs'), Parse.bind_eq hpa, Parse.bind_eq (Parse.peek_eq hs₁),
      updateOp_symbol hok]
    simp only [hno, hsim, Bool.false_eq_true, ↓reduceIte, Parse.pure_bind]
    rw [Parse.bind_eq (Parse.discard_eq (Parse.advance_cons hs₁ hr)), Parse.bind_eq (Parse.spanFrom_eq _ _)]
    rfl
  · have he' : e.wfAt T .lhs = true := by
      rw [← wfAt_postfix_eq (fun sp op arg h' => hp ⟨sp, op, arg, h'⟩)]; exact he
    obtain ⟨arg', s₁, hpa, hea, hL₁⟩ := hL e (Nat.le_refl _) he' s (x :: ts') rest hT hs hl ht hn hr hends.1 ha
    obtain ⟨u, r, rfl⟩ := List.exists_cons_of_ne_nil hr
    have hs₁ : s₁.rest = u :: r := hL₁.rest_eq
    refine ⟨arg', s₁, ?_, hea, hL₁⟩
    simp only [Parse.parsePostfix]
    rw [Parse.bind_eq (Parse.peek_eq hs'), Parse.bind_eq hpa, Parse.bind_eq (Parse.peek_eq hs₁)]
    by_cases hu : u.kind = .punct "++" ∨ u.kind = .punct "--"
    · have hnl := hends.2 u rfl hu
      rcases hu with hu | hu
      · rw [updateOp_symbol (op := .increment) (by simpa [UpdateOp.symbol] using hu)]
        simp [hnl, pure, EStateM.pure]
      · rw [updateOp_symbol (op := .decrement) (by simpa [UpdateOp.symbol] using hu)]
        simp [hnl, pure, EStateM.pure]
    · simp at hu
      simp [Parse.updateOp?, Token.isPunct, hu, pure, EStateM.pure]

/-- A unary or prefix operator, or what `parsePostfix` reads. -/
theorem parseUnary_reads {T : Edition} (f : Nat) (e : Expr) (he : e.wfAt T .unary = true)
    (hU : ∀ x : Expr, x.height < e.height → x.wfAt T .unary = true →
      ReadsE T (Parse.parseUnary f) x EndsPostfix)
    (hL : ∀ x : Expr, x.height < e.height → x.wfAt T .lhs = true →
      ReadsE T (Parse.parseLeftHandSide f) x EndsLhs)
    (hP : e.wfAt T .postfix = true → ReadsE T (Parse.parsePostfix f) e EndsPostfix) :
    ReadsE T (Parse.parseUnary (f + 1)) e EndsPostfix := by
  intro s ts rest hT hs hl ht hn hr hends ha
  by_cases hu : ∃ sp op arg, e = .unary sp op arg
  · obtain ⟨sp, op, arg, rfl⟩ := hu
    simp only [Expr.wfAt] at he
    obtain ⟨k, hk, hop⟩ := unaryOp_symbol op
    obtain ⟨o, ats, rfl, hok, hat⟩ := Touching.cons_one (by simpa [Expr.words, hk] using ht)
    have hs' : s.rest = o :: (ats ++ rest) := by simpa using hs
    let s₁ : ParseState := { s with rest := ats ++ rest, left := s.left - 1, lastStop := o.span.stop }
    obtain ⟨arg', s₂, hpa, hea, hL₂⟩ := hU arg (by simp [Expr.height]) he s₁ ats rest hT rfl
      (by simp [s₁, hl, hs']) hat (fun y hy => hn y (by simp [List.mem_of_mem_tail hy])) hr hends
      (by simpa [Expr.afterOK] using ha)
    refine ⟨.unary ⟨o.span.start, s₂.lastStop⟩ op arg', s₂, ?_, by simp [Expr.erase, hea],
      leaves_trans (leaves_advance hs' hl) hL₂⟩
    simp only [Parse.parseUnary]
    rw [Parse.bind_eq (Parse.peek_eq hs'), hop o hok]
    dsimp only
    rw [Parse.bind_eq (Parse.discard_eq (Parse.advance_cons hs' (by simp [hr]))), Parse.bind_eq hpa,
      Parse.bind_eq (Parse.spanFrom_eq _ _)]
    rfl
  by_cases hpr : ∃ sp op arg, e = .prefix sp op arg
  · obtain ⟨sp, op, arg, rfl⟩ := hpr
    simp only [Expr.wfAt, Bool.and_eq_true] at he
    obtain ⟨o, ats, rfl, hok, hat⟩ := Touching.cons_one (by simpa [Expr.words, punctWord] using ht)
    have hs' : s.rest = o :: (ats ++ rest) := by simpa using hs
    let s₁ : ParseState := { s with rest := ats ++ rest, left := s.left - 1, lastStop := o.span.stop }
    obtain ⟨arg', s₂, hpa, hea, hL₂⟩ := hL arg (by simp [Expr.height]) he.1 s₁ ats rest hT rfl
      (by simp [s₁, hl, hs']) hat (fun y hy => hn y (by simp [List.mem_of_mem_tail hy])) hr hends.1
      (by simpa [Expr.afterOK] using ha)
    have hsim : arg'.isSimpleTarget = true := by rw [isSimpleTarget_of_erase hea]; exact he.2
    have hnone : Parse.unaryOp? o = none := by
      cases op <;> simp [Parse.unaryOp?, hok, UpdateOp.symbol]
    refine ⟨.prefix ⟨o.span.start, s₂.lastStop⟩ op arg', s₂, ?_, by simp [Expr.erase, hea],
      leaves_trans (leaves_advance hs' hl) hL₂⟩
    simp only [Parse.parseUnary]
    rw [Parse.bind_eq (Parse.peek_eq hs'), hnone, updateOp_symbol hok]
    simp only [Parse.pure_bind]
    rw [Parse.bind_eq (Parse.discard_eq (Parse.advance_cons hs' (by simp [hr]))), Parse.bind_eq hpa]
    simp only [hsim, ↓reduceIte, Parse.pure_bind]
    rw [Parse.bind_eq (Parse.spanFrom_eq _ _)]
    rfl
  · have he' : e.wfAt T .postfix = true := by
      rw [← wfAt_unary_eq (fun sp op arg h' => hu ⟨sp, op, arg, h'⟩)
        (fun sp op arg h' => hpr ⟨sp, op, arg, h'⟩)]; exact he
    obtain ⟨k, hk, hsk⟩ := Expr.firstPostfix e he'
    obtain ⟨x, ts', rfl, hxk⟩ : ∃ x ts', ts = x :: ts' ∧ x.kind = k := by
      have hk' : (ts.map (·.kind)).head? = some k := by rw [ht.kinds]; exact hk
      cases ts with
      | nil => simp at hk'
      | cons x ts' => simp at hk'; exact ⟨x, ts', rfl, hk'⟩
    have hs' : s.rest = x :: (ts' ++ rest) := by simpa using hs
    obtain ⟨e', s', hp, hee, hL'⟩ := hP he' s (x :: ts') rest hT hs hl ht hn hr hends ha
    refine ⟨e', s', ?_, hee, hL'⟩
    simp only [Parse.parseUnary]
    rw [Parse.bind_eq (Parse.peek_eq hs'), unaryOp_none (hxk ▸ hsk), updateOp_none (hxk ▸ hsk)]
    exact hp

/-! ### Binary operators -/

theorem BinOp.beq_eq (a b : BinOp) : (a == b) = decide (a = b) := by
  cases a <;> cases b <;> rfl

instance : LawfulBEq BinOp where
  eq_of_beq {a b} h := by rw [BinOp.beq_eq] at h; exact of_decide_eq_true h
  rfl {a} := by rw [BinOp.beq_eq]; exact decide_eq_true rfl

/-- The operand that a chain of binary operators starts with. -/
def binHead : Expr → Expr
  | .binary _ _ l _ | .asConst _ l | .satisfies _ l _ => binHead l
  | e => e

/-- The words of the operators and right operands of a chain, after its head. -/
def binSuffix : Expr → List Word
  | .binary _ op l r => binSuffix l ++ symbol op.symbol :: r.words
  | .asConst _ l => binSuffix l ++ [identWord "as", keywordWord "const"]
  | .satisfies _ l t => binSuffix l ++ identWord "satisfies" :: t.words
  | _ => []

/-- The number of operators of a chain. -/
def binSteps : Expr → Nat
  | .binary _ _ l _ | .asConst _ l | .satisfies _ l _ => binSteps l + 1
  | _ => 0

/-- What may follow the last right operand of a chain. -/
def NextOp : Expr → List Token → Prop
  | .binary _ op _ _, rest => EndsBin (rhsPrec op) rest
  | _, _ => True

theorem words_bin (e : Expr) : e.words = (binHead e).words ++ binSuffix e := by
  cases e with
  | binary _ op l r => simp [binHead, binSuffix, Expr.words, words_bin l]
  | asConst _ l => simp [binHead, binSuffix, Expr.words, words_bin l]
  | satisfies _ l t => simp [binHead, binSuffix, Expr.words, words_bin l]
  | _ => simp [binHead, binSuffix]

theorem wf_binHead {T : Edition} {m : Nat} (e : Expr) (h : e.wfAt T (.bin m) = true) :
    (binHead e).wfAt T .unary = true := by
  cases e with
  | binary _ op l r =>
    simp only [Expr.wfAt, Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨⟨⟨_, _⟩, hl⟩, _⟩, _⟩, _⟩, _⟩ := h
    simpa [binHead] using wf_binHead l hl
  | asConst _ l =>
    simp only [Expr.wfAt, Bool.and_eq_true] at h
    simpa [binHead] using wf_binHead l h.1.2
  | satisfies _ l t =>
    simp only [Expr.wfAt, Bool.and_eq_true] at h
    simpa [binHead] using wf_binHead l h.1.1.2
  | _ => simp_all [binHead, Expr.wfAt]

theorem afterOK_binHead (e : Expr) (after : List TokenKind) (h : e.afterOK after = true) :
    (binHead e).afterOK ((binSuffix e).flatten ++ after) = true := by
  cases e with
  | binary _ op l r =>
    simp only [Expr.afterOK, Bool.and_eq_true] at h
    simpa [binHead, binSuffix, Expr.tokens] using afterOK_binHead l _ h.1.2
  | asConst _ l =>
    simp only [Expr.afterOK] at h
    simpa [binHead, binSuffix, identWord, keywordWord] using afterOK_binHead l _ h
  | satisfies _ l t =>
    simp only [Expr.afterOK] at h
    simpa [binHead, binSuffix, identWord, TypeExpr.tokens] using afterOK_binHead l _ h
  | _ => simpa [binHead, binSuffix] using h

theorem height_binHead (e : Expr) : (binHead e).height ≤ e.height := by
  cases e with
  | binary _ op l r => have := height_binHead l; simp [binHead, Expr.height]; omega
  | asConst _ l => have := height_binHead l; simp [binHead, Expr.height]; omega
  | satisfies _ l t => have := height_binHead l; simp [binHead, Expr.height]; omega
  | _ => simp [binHead]

theorem binSteps_le (e : Expr) : binSteps e ≤ (binSuffix e).flatten.length := by
  cases e with
  | binary _ op l r =>
    have := binSteps_le l
    obtain ⟨k, ks, hk, _⟩ := binOp_head op
    simp [binSteps, binSuffix, hk] at this ⊢; omega
  | asConst _ l =>
    have := binSteps_le l
    simp [binSteps, binSuffix, identWord, keywordWord] at this ⊢; omega
  | satisfies _ l t =>
    have := binSteps_le l
    simp [binSteps, binSuffix, identWord] at this ⊢; omega
  | _ => simp [binSteps]

/-- The tokens after the head of a chain start with an operator, if there are any. -/
theorem binSuffix_first : ∀ e : Expr, (binSuffix e).flatten = [] ∨
    ∃ k ks, (binSuffix e).flatten = k :: ks ∧ stopsPostfix k = true
  | .binary _ op l r => by
    rcases binSuffix_first l with h | ⟨k, ks, h, hk⟩
    · obtain ⟨k, ks, hs, hk⟩ := binOp_head op
      exact .inr ⟨k, ks ++ r.words.flatten, by simp [binSuffix, h, hs], hk⟩
    · exact .inr ⟨k, ks ++ (symbol op.symbol ++ r.words.flatten), by simp [binSuffix, h], hk⟩
  | .asConst _ l => by
    rcases binSuffix_first l with h | ⟨k, ks, h, hk⟩
    · exact .inr ⟨.ident "as", [.keyword "const"], by simp [binSuffix, h, identWord, keywordWord], rfl⟩
    · exact .inr ⟨k, ks ++ [.ident "as", .keyword "const"], by simp [binSuffix, h, identWord, keywordWord], hk⟩
  | .satisfies _ l t => by
    rcases binSuffix_first l with h | ⟨k, ks, h, hk⟩
    · exact .inr ⟨.ident "satisfies", t.words.flatten, by simp [binSuffix, h, identWord], rfl⟩
    · exact .inr ⟨k, ks ++ (.ident "satisfies" :: t.words.flatten), by simp [binSuffix, h, identWord], hk⟩
  | .ident .. | .number .. | .bigint .. | .string .. | .bool .. | .null _ | .array .. | .object ..
  | .paren .. | .member .. | .optMember .. | .index .. | .call .. | .unary .. | .prefix .. | .postfix ..
  | .cond .. | .assign .. | .arrow .. | .new .. | .spread .. => .inl (by simp [binSuffix])

theorem Expr.isLogical_erase (e : Expr) : e.erase.isLogical = e.isLogical := by
  cases e with
  | binary _ op l r => cases op <;> simp [Expr.erase, Expr.isLogical]
  | _ => simp [Expr.erase, Expr.isLogical]

theorem Expr.isCoalesce_erase (e : Expr) : e.erase.isCoalesce = e.isCoalesce := by
  cases e with
  | binary _ op l r => cases op <;> simp [Expr.erase, Expr.isCoalesce]
  | _ => simp [Expr.erase, Expr.isCoalesce]

theorem isLogical_of_erase {e e' : Expr} (h : e'.erase = e.erase) : e'.isLogical = e.isLogical := by
  rw [← Expr.isLogical_erase e', h, Expr.isLogical_erase]

theorem isCoalesce_of_erase {e e' : Expr} (h : e'.erase = e.erase) : e'.isCoalesce = e.isCoalesce := by
  rw [← Expr.isCoalesce_erase e', h, Expr.isCoalesce_erase]

theorem notUnary_of_erase {e e' : Expr} (h : e'.erase = e.erase) (he : ∀ sp o x, e ≠ .unary sp o x) :
    ∀ sp o x, e' ≠ .unary sp o x := by
  rintro sp o x rfl
  cases e <;> simp [Expr.erase] at h
  exact he _ _ _ rfl

/-- `**` binds tighter than every other operator. -/
theorem precedence_lt_exp {op : BinOp} (h : op ≠ .exp) : op.precedence < BinOp.exp.precedence := by
  cases op <;> simp_all [BinOp.precedence]

/-- The loop stops before an operator that binds less tightly than `m`. -/
theorem binStep_stop {pr : Nat → ParseM Expr} {pt : ParseM TypeExpr} {start : Pos} {m : Nat} {acc : Expr}
    {s : ParseState} (h : EndsBin m s.rest) (hr : s.rest ≠ []) :
    Parse.binaryStep pr pt start m acc s = .ok (acc, false) s := by
  obtain ⟨o, ho, hp⟩ := h.2.1 s rfl
  obtain ⟨u, r, hur⟩ := List.exists_cons_of_ne_nil hr
  simp only [Parse.binaryStep]
  rw [Parse.bind_eq ho]
  rcases o with _ | ⟨op, w⟩
  · have hnt := h.2.2 u (by simp [hur])
    simp only [Parse.typeOperatorStep]
    rw [Parse.bind_eq (Parse.peek_eq hur)]
    by_cases ht : Parse.isTypeOperator u = true
    · simp [ht, hnt ht, pure, EStateM.pure]
    · simp [ht, pure, EStateM.pure]
  · have := hp op w rfl
    simp [this, pure, EStateM.pure]

theorem peekBinaryOp_ident {s : ParseState} {x : Token} {r : List Token} {n : String} (hs : s.rest = x :: r)
    (hx : x.kind = .ident n) : Parse.peekBinaryOp s = .ok none s := by
  simp [Parse.peekBinaryOp, Parse.peek_eq hs, hx, bind, EStateM.bind, pure, EStateM.pure]

/-- `as const`, which a token that is none of `typeEnders` follows. -/
theorem asStep_go {pr : Nat → ParseM Expr} {pt : ParseM TypeExpr} {start : Pos} {m : Nat} {acc : Expr}
    {s : ParseState} {x c u : Token} {r : List Token}
    (hs : s.rest = x :: c :: u :: r) (hx : x.kind = .ident "as") (hxn : x.newlineBefore = false)
    (hc : c.kind = .keyword "const") (hu : ∀ p, u.kind = .punct p → p ∉ Parse.typeEnders)
    (hm : m ≤ BinOp.lt.precedence) (hacc : Parse.refusedBeforeType acc = false) :
    Parse.binaryStep pr pt start m acc s =
      .ok (.asConst ⟨start, c.span.stop⟩ acc, true) (past (past s x (c :: u :: r)) c (u :: r)) := by
  have hnt : ¬ BinOp.lt.precedence < m := by omega
  have hue : ¬ ∃ q, q ∈ Parse.typeEnders ∧ u.isPunct q = true := by
    rintro ⟨q, hq, h⟩
    simp only [Token.isPunct, beq_iff_eq] at h
    exact hu q h hq
  simp [Parse.binaryStep, peekBinaryOp_ident hs hx, Parse.typeOperatorStep, Parse.peek_eq hs,
    Parse.isTypeOperator, Token.isIdent, hx, hxn, hnt, hacc, Parse.advance_eq hs,
    Parse.peek_eq (s := past s x (c :: u :: r)) rfl,
    Parse.advance_eq (s := past s x (c :: u :: r)) rfl, Parse.peek_eq (s := past (past s x (c :: u :: r)) c (u :: r)) rfl,
    discard, Functor.mapConst, EStateM.map, Token.isKeyword, hc, Parse.refuseAfterType, hue, Parse.spanFrom,
    bind, EStateM.bind, pure, EStateM.pure, get, getThe, MonadStateOf.get, EStateM.get]

/-- `satisfies T`, where `pt` reads `T`, which a token that is none of
`typeEnders` follows. -/
theorem satisfiesStep_go {pr : Nat → ParseM Expr} {pt : ParseM TypeExpr} {start : Pos} {m : Nat} {acc : Expr}
    {s s₁ : ParseState} {x u : Token} {r rest : List Token} {t : TypeExpr}
    (hs : s.rest = x :: rest) (hne : rest ≠ []) (hx : x.kind = .ident "satisfies") (hxn : x.newlineBefore = false)
    (hp : pt (past s x rest) = .ok t s₁) (hs₁ : s₁.rest = u :: r)
    (hu : ∀ p, u.kind = .punct p → p ∉ Parse.typeEnders) (hm : m ≤ BinOp.lt.precedence)
    (hacc : Parse.refusedBeforeType acc = false) :
    Parse.binaryStep pr pt start m acc s = .ok (.satisfies ⟨start, s₁.lastStop⟩ acc t, true) s₁ := by
  have hnt : ¬ BinOp.lt.precedence < m := by omega
  have hue : ¬ ∃ q, q ∈ Parse.typeEnders ∧ u.isPunct q = true := by
    rintro ⟨q, hq, h⟩
    simp only [Token.isPunct, beq_iff_eq] at h
    exact hu q h hq
  simp [Parse.binaryStep, peekBinaryOp_ident hs hx, Parse.typeOperatorStep, Parse.peek_eq hs,
    Parse.isTypeOperator, Token.isIdent, hx, hxn, hnt, hacc, Parse.advance_cons hs hne, hp, Parse.peek_eq hs₁,
    discard, Functor.mapConst, EStateM.map, Parse.refuseAfterType, hue, Parse.spanFrom,
    bind, EStateM.bind, pure, EStateM.pure, get, getThe, MonadStateOf.get, EStateM.get]

theorem refusedBeforeType_of_erase {e e' : Expr} (h : e'.erase = e.erase) :
    Parse.refusedBeforeType e' = Parse.refusedBeforeType e := by
  cases e <;> cases e' <;> simp_all [Expr.erase, Parse.refusedBeforeType]

theorem leftOKType_refused {l : Expr} (h : leftOKType l = true) : Parse.refusedBeforeType l = false := by
  cases l <;> simp_all [leftOKType, Parse.refusedBeforeType]

/-- An operator that `BinOp.followsType` allows may follow a type. -/
theorem typeOK_binOp {op : BinOp} {a rest : List Token} (h : op.followsType = true)
    (ha : a.map (·.kind) = symbol op.symbol) : TypeOK (a ++ rest) := by
  intro u hu p hp hmem
  cases a with
  | nil => cases op <;> simp [BinOp.symbol, symbol, Lex.reservedWords, punctWord, keywordWord] at ha
  | cons x a' =>
    simp only [List.cons_append, List.head?_cons, Option.mem_def, Option.some.injEq] at hu
    obtain rfl := hu
    simp only [List.map_cons] at ha
    simp only [Parse.typeEnders, List.mem_cons, List.not_mem_nil, or_false] at hmem
    cases op <;> simp [BinOp.followsType] at h <;>
      simp [BinOp.symbol, symbol, Lex.reservedWords, punctWord, keywordWord, hp] at ha <;>
      (try obtain ⟨ha, -⟩ := ha) <;> subst ha <;> simp at hmem

theorem typeOK_cons {u : Token} {r : List Token} (h : TypeOK (u :: r)) :
    ∀ p, u.kind = .punct p → p ∉ Parse.typeEnders := h u rfl

theorem noTypeOk_ident {x : Token} {r : List Token} {n : String} (hx : x.kind = .ident n) : TypeOK (x :: r) := by
  intro u hu p hp
  simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hu
  subst hu; rw [hx] at hp; cases hp

/-- What ends a conditional expression ends one that ends in a type. -/
theorem typeOK_of_endsCond {rest : List Token} (h : EndsCond rest) : TypeOK rest := by
  intro u hu p hp hmem
  cases rest with
  | nil => simp at hu
  | cons x r =>
    simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hu
    obtain rfl := hu
    have hl := h.1.1.1 x rfl
    have hq := h.2 x rfl
    obtain ⟨o, ho, hop⟩ := h.1.2.1 { rest := x :: r, left := 0, eof := x } rfl
    simp only [Parse.typeEnders, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact hq hp
      | exact hl.1 hp
      | exact hl.2.1 hp
      | exact hl.2.2.1 hp
      | (simp [Parse.peekBinaryOp, Parse.peek, Parse.peekAt, hp, BinOp.ofSymbol?, BinOp.all, BinOp.symbol, bind,
            EStateM.bind, pure, EStateM.pure, get, getThe, MonadStateOf.get, EStateM.get] at ho
         subst ho; exact absurd (hop _ _ rfl) (Nat.not_lt_zero _))

theorem followsType_of {u : Token} {r : List Token} (h : ∀ p, u.kind = .punct p → p ∉ Parse.typeEnders) :
    FollowsType (u :: r) := by
  refine ⟨⟨fun t ht => ?_, fun t ht => ?_⟩, fun t ht => ?_⟩ <;> simp at ht <;> subst ht
  · exact ⟨fun e => h "<" e (by decide), fun e => h "." e (by decide)⟩
  · exact fun e => h "[" e (by decide)
  · exact ⟨fun e => h "|" e (by decide), fun e => h "&" e (by decide)⟩

/-- `as` or `satisfies` ends the right operand of an operator that binds
more tightly than `<`. -/
theorem endsBin_typeOp {k : Nat} {x : Token} {r : List Token} {n : String} (hx : x.kind = .ident n)
    (hk : BinOp.lt.precedence < k) : EndsBin k (x :: r) :=
  ⟨endsPostfix_of (by simp [hx, stopsPostfix]), fun s hs => ⟨none, peekBinaryOp_ident hs hx, by simp⟩,
    fun _ _ _ => hk⟩

theorem nextOp_type {l : Expr} (hl : leftOKType l = true) {x : Token} {r : List Token} {n : String}
    (hx : x.kind = .ident n) : NextOp l (x :: r) := by
  cases l with
  | binary sp op' l' r' =>
    simp only [leftOKType, decide_eq_true_eq] at hl
    refine endsBin_typeOp hx ?_
    unfold rhsPrec
    split
    · rename_i h; simp at h; subst h; simp [BinOp.precedence]
    · omega
  | _ => trivial


/-- One operator and its right operand, which `pr` reads. -/
theorem binStep_go {pr : Nat → ParseM Expr} {pt : ParseM TypeExpr} {start : Pos} {m : Nat} {acc rhs : Expr}
    {s s₁ s₂ : ParseState} {op : BinOp} {a b : List Token}
    (hs : s.rest = a ++ b) (ha : a.map (·.kind) = symbol op.symbol) (hc : Chained a)
    (hb : ∃ u r, b = u :: r ∧ startsExpr u.kind = true) (hm : m ≤ op.precedence)
    (hexp : op = .exp → ∀ sp o x, acc ≠ .unary sp o x)
    (hlt : op = .lt ∨ op = .shl → Parse.closesTypeArguments 0 b = false)
    (hT : op.allowedIn s.target = true)
    (hskip : Parse.skip a.length s = .ok () s₁)
    (hp : pr (rhsPrec op) s₁ = .ok rhs s₂)
    (hmix : ((op == .coalesce && (acc.isLogical || rhs.isLogical)) ||
      ((op == .and || op == .or) && (acc.isCoalesce || rhs.isCoalesce))) = false) :
    Parse.binaryStep pr pt start m acc s = .ok (.binary ⟨start, s₂.lastStop⟩ op acc rhs, true) s₂ := by
  obtain ⟨u, r, rfl, hu⟩ := hb
  have hpk := peekBinaryOp_op hs ha hc hu
  obtain ⟨k, ks, hk, _⟩ := binOp_head op
  obtain ⟨x, a', rfl, hx, _⟩ := List.map_eq_cons_iff.mp (ha.trans hk)
  have hs' : s.rest = x :: (a' ++ u :: r) := by simp [hs]
  have hp' := hp
  unfold rhsPrec at hp'
  simp only [BinOp.allowedIn, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq] at hT
  simp only [Parse.binaryStep]
  rw [Parse.bind_eq hpk]
  dsimp only
  rw [if_neg (by omega), Parse.pure_bind, Parse.bind_eq (Parse.peek_eq hs')]
  rw [Parse.ite_guard ?g1, Parse.ite_guard ?g2, Parse.ite_guard ?g3, Parse.ite_guard ?g4, Parse.bind_eq hskip,
    Parse.bind_eq hp', Parse.ite_guard ?g5, Parse.bind_eq (Parse.spanFrom_eq _ _)]
  · rfl
  case g1 =>
    intro h
    simp only [Bool.and_eq_true, BinOp.beq_eq, decide_eq_true_eq] at h
    obtain ⟨rfl, h⟩ := h
    cases acc <;> simp at h
    exact absurd rfl (hexp rfl _ _ _)
  case g2 =>
    intro h
    simp only [Bool.or_eq_true, BinOp.beq_eq, decide_eq_true_eq] at h
    have hc' := hlt h
    have ha' : a' = [] := by
      rcases h with rfl | rfl <;> simp [BinOp.symbol, symbol, Lex.reservedWords, punctWord] at ha <;>
        exact ha.2
    subst ha'
    simp [Parse.refuseTypeArgumentLookalike, hs', hc', get, getThe, MonadStateOf.get, EStateM.get, bind,
      EStateM.bind, pure, EStateM.pure]
  case g3 =>
    intro h
    simp only [BinOp.beq_eq, decide_eq_true_eq] at h
    exact Parse.requireFeature_ok (hT.1.resolve_left (by rw [h]; decide))
  case g4 =>
    intro h
    simp only [BinOp.beq_eq, decide_eq_true_eq] at h
    exact Parse.requireFeature_ok (hT.2.resolve_left (by rw [h]; decide))
  case g5 =>
    intro h; rw [hmix] at h; cases h


theorem leftOK_exp {l : Expr} (h : leftOK .exp l = true) : ∀ sp o x, l ≠ .unary sp o x := by
  rintro sp o x rfl; simp [leftOK] at h

theorem le_rhsPrec (op : BinOp) : op.precedence ≤ rhsPrec op := by
  unfold rhsPrec; split <;> omega

/-- The left operand of `op` ends before `op`. -/
theorem nextOp_left {op : BinOp} {l : Expr} (hl : leftOK op l = true) {a : List Token} {u : Token}
    {r : List Token} (ha : a.map (·.kind) = symbol op.symbol) (hc : Chained a) (hu : startsExpr u.kind = true) :
    NextOp l (a ++ u :: r) := by
  cases l with
  | binary sp op' l' r' =>
    simp only [leftOK, Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at hl
    refine endsBin_binOp ha hc hu ?_
    unfold rhsPrec
    split
    · rename_i h; simp at h; subst h; exact precedence_lt_exp hl.1
    · omega
  | _ => trivial

/-- The loop of `parseBinary` reads the operators and right operands of a
chain after its head, and goes on with what follows them. -/
theorem bin_loop {T : Edition} {pr : Nat → ParseM Expr} {pt : ParseM TypeExpr} {start : Pos} {m H K : Nat}
    (hR : ∀ (x : Expr) (k : Nat), x.height < H → x.wfAt T (.bin k) = true → ReadsE T (pr k) x (Ends (.bin k) x))
    (hTy : ∀ t : TypeExpr, t.wf = true → t.tokens.length ≤ K → Reads pt t FollowsType) :
    ∀ (e : Expr), e.wfAt T (.bin m) = true → e.height ≤ H →
      ∀ (n : Nat) (acc : Expr) (s : ParseState) (ts rest : List Token),
      acc.erase = (binHead e).erase → s.target = T → s.rest = ts ++ rest → s.left = s.rest.length →
      Touching ts (binSuffix e) → (∀ y ∈ ts, NoBreak y) → rest ≠ [] → ts.length ≤ K →
      NextOp e rest → (e.endsInType = true → TypeOK rest) → e.afterOK (rest.map (·.kind)) = true →
      ∃ e' s', Parse.iterate (n + binSteps e) acc (Parse.binaryStep pr pt start m) s =
        Parse.iterate n e' (Parse.binaryStep pr pt start m) s' ∧ e'.erase = e.erase ∧ Leaves s s' rest := by
  intro e he hH n acc s ts rest hacc hT hs hl ht hn hr hK hnext hTR ha
  cases e with
  | binary sp op l r =>
    simp only [Expr.wfAt, Bool.and_eq_true, decide_eq_true_eq] at he
    obtain ⟨⟨⟨⟨⟨⟨hm, hA⟩, hlw⟩, hrw⟩, hlo⟩, hmix⟩, htl⟩ := he
    have hHl : l.height ≤ H := by simp [Expr.height] at hH; omega
    have hHr : r.height < H := by simp [Expr.height] at hH; omega
    simp only [binSuffix] at ht
    obtain ⟨lts, more, rfl, hlt, hmore⟩ := Touching.append_split ht
    obtain ⟨a, b, rfl, ha', hc, hb⟩ := hmore
    obtain ⟨u, b', rfl, hu⟩ := Touching.head hb
    simp only [Expr.afterOK, Bool.and_eq_true] at ha
    obtain ⟨⟨hclose, hla⟩, hra⟩ := ha
    obtain ⟨l', s₁, hit, hel, hL⟩ := bin_loop (start := start) hR hTy l hlw hHl (n + 1) acc s lts
      (a ++ u :: (b' ++ rest))
      (by simpa [binHead] using hacc) hT (by simp [hs]) hl hlt (fun y hy => hn y (by simp [hy]))
      (by simp) (by simp at hK; omega) (nextOp_left hlo ha' (hc.chained ha') hu)
      (fun hle => typeOK_binOp (by simpa [hle] using htl) ha')
      (by rw [List.map_append, ha', ← List.cons_append, List.map_append, hb.kinds]
          simpa [Expr.tokens, List.append_assoc] using hla)
    have hs₁ : s₁.rest = a ++ u :: (b' ++ rest) := hL.rest_eq
    have hl₁ : s₁.left = s₁.rest.length := by rw [hL.left_eq, hL.rest_eq]
    obtain ⟨s₁', hsk, hLk⟩ := Parse.skip_ok a hs₁ (by simp) hl₁
    have hl₁' : s₁'.left = s₁'.rest.length := by rw [hLk.left_eq, hLk.rest_eq]
    obtain ⟨r', s₂, hpr, her, hLr⟩ := hR r (rhsPrec op) hHr hrw s₁' (u :: b') rest
      (hLk.target_eq.trans (hL.target_eq.trans hT)) (by simpa using hLk.rest_eq) hl₁' hb
      (fun y hy => hn y (by simp at hy ⊢; simp [hy])) hr ⟨hnext, fun h => hTR (by simpa [Expr.endsInType] using h)⟩
      hra
    have hexp : op = .exp → ∀ sp o x, l' ≠ .unary sp o x := fun h =>
      notUnary_of_erase hel (leftOK_exp (h ▸ hlo))
    have hlt' : op = .lt ∨ op = .shl → Parse.closesTypeArguments 0 (u :: (b' ++ rest)) = false := by
      intro h
      have hc' : (op == .lt || op == .shl) = true := by rcases h with rfl | rfl <;> rfl
      rw [hc'] at hclose
      simp only [if_true, Bool.not_eq_true'] at hclose
      rw [closesTypeArguments_kinds]
      rw [show (u :: (b' ++ rest)).map (·.kind) = r.tokens ++ rest.map (·.kind) by
        rw [← List.cons_append, List.map_append, hb.kinds]; rfl]
      exact hclose
    have hT' : op.allowedIn s₁.target = true := by rw [hL.target_eq, hT]; exact hA
    have hmix' : ((op == .coalesce && (l'.isLogical || r'.isLogical)) ||
        ((op == .and || op == .or) && (l'.isCoalesce || r'.isCoalesce))) = false := by
      rw [isLogical_of_erase hel, isLogical_of_erase her, isCoalesce_of_erase hel, isCoalesce_of_erase her]
      cases op <;> simp at hmix ⊢ <;> exact hmix
    have hstep := binStep_go (pr := pr) (pt := pt) (start := start) (m := m) (acc := l') hs₁ ha' (hc.chained ha')
      ⟨u, b' ++ rest, rfl, hu⟩ hm hexp hlt' hT' hsk hpr hmix'
    refine ⟨.binary ⟨start, s₂.lastStop⟩ op l' r', s₂, ?_, by simp [Expr.erase, hel, her], leaves_trans hL (leaves_trans hLk hLr)⟩
    rw [show n + binSteps (.binary sp op l r) = (n + 1) + binSteps l by simp [binSteps]; omega, hit,
      Parse.iterate_true hstep]
  | asConst sp l =>
    simp only [Expr.wfAt, Bool.and_eq_true, decide_eq_true_eq] at he
    obtain ⟨⟨hm, hlw⟩, hlo⟩ := he
    have hHl : l.height ≤ H := by simp [Expr.height] at hH; omega
    simp only [binSuffix] at ht
    obtain ⟨lts, more, rfl, hlt, hmore⟩ := Touching.append_split ht
    obtain ⟨x, more', rfl, hx, hmore'⟩ := Touching.cons_one (by simpa [identWord] using hmore)
    obtain ⟨c, more'', rfl, hc, hmore''⟩ := Touching.cons_one (by simpa [keywordWord] using hmore')
    have : more'' = [] := by simpa [Touching] using hmore''
    subst this
    obtain ⟨u, r, rfl⟩ := List.exists_cons_of_ne_nil hr
    simp only [Expr.afterOK] at ha
    have hat := typeOK_cons (hTR rfl)
    obtain ⟨l', s₁, hit, hel, hL⟩ := bin_loop (start := start) hR hTy l hlw hHl (n + 1) acc s lts
      (x :: c :: u :: r) (by simpa [binHead] using hacc) hT (by simp [hs]) hl hlt
      (fun y hy => hn y (by simp [hy])) (by simp) (by simp at hK; omega) (nextOp_type hlo hx)
      (fun _ => noTypeOk_ident hx) (by simpa [hx, hc] using ha)
    have hs₁ : s₁.rest = x :: c :: u :: r := hL.rest_eq
    have hl₁ : s₁.left = s₁.rest.length := by rw [hL.left_eq, hL.rest_eq]
    have hxn : x.newlineBefore = false := hn x (by simp) (by rw [hx]; simp)
    have hstep := asStep_go (pr := pr) (pt := pt) (start := start) (acc := l') hs₁ hx hxn hc
      hat hm (by rw [refusedBeforeType_of_erase hel]; exact leftOKType_refused hlo)
    refine ⟨.asConst ⟨start, c.span.stop⟩ l', _, ?_, by simp [Expr.erase, hel],
      leaves_trans hL (leaves_trans (leaves_advance hs₁ hl₁) (leaves_advance rfl (by simp [hl₁, hs₁])))⟩
    rw [show n + binSteps (.asConst sp l) = (n + 1) + binSteps l by simp [binSteps]; omega, hit,
      Parse.iterate_true hstep]
  | satisfies sp l t =>
    simp only [Expr.wfAt, Bool.and_eq_true, decide_eq_true_eq] at he
    obtain ⟨⟨⟨hm, hlw⟩, hlo⟩, htw⟩ := he
    have hHl : l.height ≤ H := by simp [Expr.height] at hH; omega
    simp only [binSuffix] at ht
    obtain ⟨lts, more, rfl, hlt, hmore⟩ := Touching.append_split ht
    obtain ⟨x, tts, rfl, hx, htts⟩ := Touching.cons_one (by simpa [identWord] using hmore)
    obtain ⟨u, r, rfl⟩ := List.exists_cons_of_ne_nil hr
    simp only [Expr.afterOK] at ha
    have hat := typeOK_cons (hTR rfl)
    obtain ⟨l', s₁, hit, hel, hL⟩ := bin_loop (start := start) hR hTy l hlw hHl (n + 1) acc s lts
      (x :: (tts ++ u :: r)) (by simpa [binHead] using hacc) hT (by simp [hs]) hl hlt
      (fun y hy => hn y (by simp [hy])) (by simp) (by simp at hK; omega) (nextOp_type hlo hx)
      (fun _ => noTypeOk_ident hx)
      (by rw [List.map_cons, List.map_append, htts.kinds, hx]; simpa [TypeExpr.tokens] using ha)
    have hs₁ : s₁.rest = x :: (tts ++ u :: r) := hL.rest_eq
    have hl₁ : s₁.left = s₁.rest.length := by rw [hL.left_eq, hL.rest_eq]
    have hxn : x.newlineBefore = false := hn x (by simp) (by rw [hx]; simp)
    have htk : tts.length ≤ K := by simp at hK; omega
    have hlen : t.tokens.length ≤ K := by
      rw [TypeExpr.tokens, ← htts.kinds, List.length_map]; exact htk
    obtain ⟨t', s₂, hpt, het, hL₂⟩ := hTy t htw hlen (past s₁ x (tts ++ u :: r)) tts (u :: r) rfl
      (by simp [hl₁, hs₁]) (by rw [htts.kinds]; rfl) (fun y hy => hn y (by simp [hy])) (by simp)
      (followsType_of hat)
    have hstep := satisfiesStep_go (pr := pr) (start := start) (acc := l') hs₁ (by simp) hx hxn hpt
      hL₂.rest_eq hat hm (by rw [refusedBeforeType_of_erase hel]; exact leftOKType_refused hlo)
    refine ⟨.satisfies ⟨start, s₂.lastStop⟩ l' t', s₂, ?_, by simp [Expr.erase, hel, het],
      leaves_trans hL (leaves_trans (leaves_advance hs₁ hl₁) hL₂)⟩
    rw [show n + binSteps (.satisfies sp l t) = (n + 1) + binSteps l by simp [binSteps]; omega, hit,
      Parse.iterate_true hstep]
  | _ =>
    simp [binSuffix, Touching] at ht; subst ht
    exact ⟨acc, s, by simp [binSteps], by simpa [binHead] using hacc,
      Leaves.refl (by simpa using hs) (by simp [hl, hs])⟩


/-- A chain of binary operators. -/
theorem parseBinary_reads {T : Edition} (f m : Nat) (e : Expr) (he : e.wfAt T (.bin m) = true)
    (hU : ReadsE T (Parse.parseUnary f) (binHead e) EndsPostfix)
    (hR : ∀ (x : Expr) (k : Nat), x.height < e.height → x.wfAt T (.bin k) = true →
      ReadsE T (Parse.parseBinary f k) x (Ends (.bin k) x)) :
    ReadsE T (Parse.parseBinary (f + 1) m) e (Ends (.bin m) e) := by
  intro s ts rest hT hs hl ht hn hr hends ha
  rw [words_bin] at ht
  obtain ⟨hts, sts, rfl, hht, hst⟩ := Touching.append_split ht
  obtain ⟨x, hts', rfl, _⟩ := Touching.head hht
  have hs' : s.rest = x :: (hts' ++ sts ++ rest) := by simpa using hs
  have hEnd : EndsPostfix (sts ++ rest) := by
    rcases binSuffix_first e with h | ⟨k, ks, h, hk⟩
    · have : sts = [] := by have := hst.kinds; rw [h] at this; simpa using this
      subst this; simpa using hends.1.1
    · obtain ⟨y, sts', rfl, hy, _⟩ := List.map_eq_cons_iff.mp (hst.kinds.trans h)
      exact endsPostfix_of (hy ▸ hk)
  obtain ⟨h', s₁, hp, heh, hL⟩ := hU s (x :: hts') (sts ++ rest) hT (by simp [hs]) hl hht
    (fun y hy => hn y (List.mem_append_left _ hy)) (by simp [hr]) hEnd
    (by rw [List.map_append, hst.kinds]; exact afterOK_binHead e _ ha)
  have hl₁ : s₁.left = s₁.rest.length := by rw [hL.left_eq, hL.rest_eq]
  have hsteps : binSteps e ≤ sts.length := by
    have h1 := binSteps_le e
    have h2 : sts.length = (binSuffix e).flatten.length := by rw [← hst.kinds, List.length_map]
    omega
  obtain ⟨k, hk⟩ : ∃ k, 10 * (s.left + 1) = (k + 1) + binSteps e :=
    ⟨10 * (s.left + 1) - 1 - binSteps e, by rw [hl, hs']; simp; omega⟩
  have hnext : NextOp e rest := by
    cases e with
    | binary sp op l r =>
      simp only [Expr.wfAt, Bool.and_eq_true, decide_eq_true_eq] at he
      exact hends.1.mono (Nat.le_trans he.1.1.1.1.1.1 (le_rhsPrec op))
    | _ => trivial
  have hTy : ∀ t : TypeExpr, t.wf = true → t.tokens.length ≤ sts.length →
      Reads (Parse.parseType (10 * (s₁.left + 1))) t FollowsType := by
    intro t ht hlen
    have h1 := TypeExpr.height_le t
    have h2 : sts.length ≤ s₁.left := by rw [hl₁, hL.rest_eq, List.length_append]; omega
    exact (types_reads _).1 t ht (by omega)
  obtain ⟨e', s₂, hit, he', hL₂⟩ := bin_loop (pr := Parse.parseBinary f) (start := x.span.start) (m := m)
    (H := e.height) hR hTy e he (Nat.le_refl _) (k + 1) h' s₁ sts rest heh (hL.target_eq.trans hT) hL.rest_eq hl₁
    hst (fun y hy => hn y (List.mem_append_right _ hy)) hr (Nat.le_refl _) hnext hends.2 ha
  refine ⟨e', s₂, ?_, he', leaves_trans hL hL₂⟩
  simp only [Parse.parseBinary]
  rw [Parse.bind_eq (Parse.peek_eq hs'), Parse.bind_eq (Parse.budget_eq _), Parse.bind_eq hp,
    Parse.bind_eq (Parse.budget_eq _), hk, hit,
    Parse.iterate_false (binStep_stop (by rw [hL₂.rest_eq]; exact hends.1) (by rw [hL₂.rest_eq]; exact hr))]

theorem wfAt_cond_eq {T : Edition} {e : Expr} (h : ∀ sp t a b, e ≠ .cond sp t a b) :
    e.wfAt T .cond = e.wfAt T (.bin 0) := by
  cases e <;> simp_all [Expr.wfAt]

theorem wfAt_assign_eq {T : Edition} {e : Expr} (h : ∀ sp op t v, e ≠ .assign sp op t v)
    (h' : ∀ sp p ps b, e ≠ .arrow sp p ps b) : e.wfAt T .assign = e.wfAt T .cond := by
  cases e <;> first | exact absurd rfl (h' _ _ _ _) | simp_all [Expr.wfAt]

theorem ends_cond_eq {e : Expr} (h : ∀ sp t a b, e ≠ .cond sp t a b) : Ends .cond e = EndsCond := by
  cases e <;> first | exact absurd rfl (h _ _ _ _) | rfl


/-- A conditional expression, or what `parseBinary` reads. -/
theorem parseConditional_reads {T : Edition} (f : Nat) (e : Expr) (he : e.wfAt T .cond = true)
    (hB : ∀ x : Expr, x.height ≤ e.height → x.wfAt T (.bin 0) = true →
      ReadsE T (Parse.parseBinary f 0) x (Ends (.bin 0) x))
    (hA : ∀ x : Expr, x.height < e.height → x.wfAt T .assign = true →
      ReadsE T (Parse.parseAssign f) x EndsAssign) :
    ReadsE T (Parse.parseConditional (f + 1)) e (Ends .cond e) := by
  intro s ts rest hT hs hl ht hn hr hends ha
  obtain ⟨x, ts', rfl, _⟩ := Touching.head ht
  have hs' : s.rest = x :: (ts' ++ rest) := by simpa using hs
  by_cases hc : ∃ sp t a b, e = .cond sp t a b
  · obtain ⟨sp, t, a, b, rfl⟩ := hc
    simp only [Expr.wfAt, Bool.and_eq_true] at he
    obtain ⟨⟨⟨hwt, hwa⟩, hwb⟩, hnt⟩ := he
    simp only [Ends] at hends
    simp only [Expr.words, List.append_assoc, List.cons_append] at ht
    obtain ⟨tts, more, hsplit, htt, hmore⟩ := Touching.append_split ht
    obtain ⟨q, more₁, rfl, hq, hm₁⟩ := Touching.cons_one (by simpa [punctWord] using hmore)
    obtain ⟨ats, more₂, rfl, hat, hm₂⟩ := Touching.append_split hm₁
    obtain ⟨c, bts, rfl, hcolon, hbt⟩ := Touching.cons_one (by simpa [punctWord] using hm₂)
    simp only [Expr.afterOK, Bool.and_eq_true] at ha
    obtain ⟨⟨hat', haa⟩, hab⟩ := ha
    have hs₀ : s.rest = tts ++ q :: (ats ++ c :: (bts ++ rest)) := by rw [hs, hsplit]; simp
    have hne : tts ≠ [] := by obtain ⟨_, _, rfl, _⟩ := Touching.head htt; simp
    obtain ⟨t', s₁, hpt, het, hL₁⟩ := hB t (by simp [Expr.height]; omega) hwt s tts
      (q :: (ats ++ c :: (bts ++ rest))) hT hs₀ hl htt (fun y hy => hn y (tail_sub hsplit hne (.inl hy))) (by simp)
      ⟨endsBin_question hq, fun h => by simp [h] at hnt⟩
      (by simpa [hq, hcolon, hat.kinds, hbt.kinds, Expr.tokens, List.append_assoc] using hat')
    have hs₁ : s₁.rest = q :: (ats ++ c :: (bts ++ rest)) := hL₁.rest_eq
    have hl₁ : s₁.left = s₁.rest.length := by rw [hL₁.left_eq, hL₁.rest_eq]
    let s₂ : ParseState := { s₁ with rest := ats ++ c :: (bts ++ rest), left := s₁.left - 1, lastStop := q.span.stop }
    obtain ⟨a', s₃, hpa, hea, hL₃⟩ := hA a (by simp [Expr.height]; omega) hwa s₂ ats (c :: (bts ++ rest))
      (hL₁.target_eq.trans hT) rfl (by simp [s₂, hl₁, hs₁]) hat
      (fun y hy => hn y (tail_sub hsplit hne (.inr (by simp [List.mem_of_mem_tail hy]))))
      (by simp) (endsAssign_separator hcolon (by simp [separators]))
      (by simpa [hcolon, hbt.kinds, Expr.tokens] using haa)
    have hs₃ : s₃.rest = c :: (bts ++ rest) := hL₃.rest_eq
    let s₄ : ParseState := { s₃ with rest := bts ++ rest, left := s₃.left - 1, lastStop := c.span.stop }
    have hl₃ : s₃.left = s₃.rest.length := by rw [hL₃.left_eq, hL₃.rest_eq]
    obtain ⟨b', s₅, hpb, heb, hL₅⟩ := hA b (by simp [Expr.height]; omega) hwb s₄ bts rest
      (hL₃.target_eq.trans (hL₁.target_eq.trans hT)) rfl (by simp [s₄, hl₃, hs₃]) hbt
      (fun y hy => hn y (tail_sub hsplit hne (.inr (by simp [List.mem_of_mem_tail hy])))) hr hends hab
    refine ⟨.cond ⟨x.span.start, s₅.lastStop⟩ t' a' b', s₅, ?_, by simp [Expr.erase, het, hea, heb],
      leaves_trans hL₁ (leaves_trans (leaves_advance hs₁ hl₁) (leaves_trans hL₃
        (leaves_trans (leaves_advance hs₃ hl₃) hL₅)))⟩
    simp only [Parse.parseConditional]
    rw [Parse.bind_eq (Parse.peek_eq hs'), Parse.bind_eq hpt, Parse.bind_eq (Parse.peek_eq hs₁)]
    simp only [Token.isPunct, hq, beq_self_eq_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      Parse.pure_bind]
    rw [Parse.bind_eq (Parse.discard_eq (Parse.advance_cons hs₁ (by simp))), Parse.bind_eq hpa,
      Parse.bind_eq (Parse.expectPunct_ok hs₃ (by simp [hr]) hcolon), Parse.bind_eq hpb,
      Parse.bind_eq (Parse.spanFrom_eq _ _)]
    rfl
  · have hne : ∀ sp t a b, e ≠ .cond sp t a b := fun sp t a b h' => hc ⟨sp, t, a, b, h'⟩
    have he' : e.wfAt T (.bin 0) = true := by rw [← wfAt_cond_eq hne]; exact he
    rw [ends_cond_eq hne] at hends
    obtain ⟨e', s₁, hp, hee, hL₁⟩ := hB e (Nat.le_refl _) he' s (x :: ts') rest hT hs hl ht hn hr
      ⟨hends.1, fun _ => typeOK_of_endsCond hends⟩ ha
    obtain ⟨u, r, rfl⟩ := List.exists_cons_of_ne_nil hr
    have hu : u.kind ≠ .punct "?" := hends.2 u rfl
    refine ⟨e', s₁, ?_, hee, hL₁⟩
    simp only [Parse.parseConditional]
    rw [Parse.bind_eq (Parse.peek_eq hs'), Parse.bind_eq hp, Parse.bind_eq (Parse.peek_eq hL₁.rest_eq)]
    simp [Token.isPunct, hu, pure, EStateM.pure]


section
variable {sp : Span}

theorem Expr.tokens_array (es : List Expr) :
    (Expr.array sp es).tokens = .punct "[" :: joined "," (es.map Expr.tokens) ++ [.punct "]"] := by
  simp [Expr.tokens, Expr.words, enclose, punctWord, separated_flatten, Expr.wordsOf_eq, List.map_map,
    Function.comp_def]; rfl

theorem Expr.tokens_object (ps : List Property) :
    (Expr.object sp ps).tokens = .punct "{" :: joined "," (ps.map Property.tokens) ++ [.punct "}"] := by
  simp [Expr.tokens, Expr.words, enclose, punctWord, separated_flatten, Property.wordsOf_eq,
    List.map_map, Function.comp_def]; rfl

theorem Expr.tokens_paren (i : Expr) : (Expr.paren sp i).tokens = .punct "(" :: i.tokens ++ [.punct ")"] := by
  simp [Expr.tokens, Expr.words, punctWord]

theorem Expr.tokens_member (o : Expr) (n : String) :
    (Expr.member sp o n).tokens = o.tokens ++ .punct "." :: propertyName n := by
  simp [Expr.tokens, Expr.words, punctWord]

theorem Expr.tokens_optMember (o : Expr) (n : String) :
    (Expr.optMember sp o n).tokens = o.tokens ++ .punct "?." :: propertyName n := by
  simp [Expr.tokens, Expr.words, punctWord]

theorem Expr.tokens_index (o i : Expr) :
    (Expr.index sp o i).tokens = o.tokens ++ .punct "[" :: i.tokens ++ [.punct "]"] := by
  simp [Expr.tokens, Expr.words, punctWord]

theorem Expr.tokens_call (c : Expr) (as : List Expr) :
    (Expr.call sp c as).tokens = c.tokens ++ .punct "(" :: joined "," (as.map Expr.tokens) ++ [.punct ")"] := by
  simp [Expr.tokens, Expr.words, enclose, punctWord, separated_flatten, Expr.wordsOf_eq, List.map_map,
    Function.comp_def]; rfl

theorem Expr.tokens_new (c : String) (ts : List TypeExpr) (as : List Expr) :
    (Expr.new sp c ts as).tokens =
      .keyword "new" :: ((TypeExpr.ref sp c ts).tokens ++
        .punct "(" :: (joined "," (as.map Expr.tokens) ++ [.punct ")"])) := by
  have h : (Expr.new sp c ts as).words =
      keywordWord "new" :: (TypeExpr.ref sp c ts).words ++ enclose "(" ")" (Expr.wordsOf as) := by
    rw [← typeArgWords_ref sp c ts]; rfl
  rw [Expr.tokens, h]
  simp [TypeExpr.tokens, enclose, punctWord, keywordWord, separated_flatten, Expr.wordsOf_eq, List.map_map,
    Function.comp_def]
  rfl

theorem Expr.tokens_unary (op : UnaryOp) (a : Expr) :
    (Expr.unary sp op a).tokens = symbol op.symbol ++ a.tokens := by
  simp [Expr.tokens, Expr.words]

theorem Expr.tokens_prefix (op : UpdateOp) (a : Expr) :
    (Expr.prefix sp op a).tokens = .punct op.symbol :: a.tokens := by
  simp [Expr.tokens, Expr.words, punctWord]

theorem Expr.tokens_postfix (op : UpdateOp) (a : Expr) :
    (Expr.postfix sp op a).tokens = a.tokens ++ [.punct op.symbol] := by
  simp [Expr.tokens, Expr.words, punctWord]

theorem Expr.tokens_binary (op : BinOp) (l r : Expr) :
    (Expr.binary sp op l r).tokens = l.tokens ++ symbol op.symbol ++ r.tokens := by
  simp [Expr.tokens, Expr.words]

theorem Expr.tokens_asConst (l : Expr) :
    (Expr.asConst sp l).tokens = l.tokens ++ .ident "as" :: [.keyword "const"] := by
  simp [Expr.tokens, Expr.words, identWord, keywordWord]

theorem Expr.tokens_satisfies (l : Expr) (t : TypeExpr) :
    (Expr.satisfies sp l t).tokens = l.tokens ++ .ident "satisfies" :: t.tokens := by
  simp [Expr.tokens, Expr.words, identWord, TypeExpr.tokens]

theorem Expr.tokens_cond (t a b : Expr) :
    (Expr.cond sp t a b).tokens = t.tokens ++ .punct "?" :: a.tokens ++ .punct ":" :: b.tokens := by
  simp [Expr.tokens, Expr.words, punctWord]

theorem Expr.tokens_assign (op : AssignOp) (t v : Expr) :
    (Expr.assign sp op t v).tokens = t.tokens ++ symbol op.symbol ++ v.tokens := by
  simp [Expr.tokens, Expr.words]

theorem Expr.tokens_arrow (parens : Bool) (ps : List Param) (b : Expr) :
    (Expr.arrow sp parens ps b).tokens = (arrowParams parens ps).flatten ++ .punct "=>" :: b.tokens := by
  simp [Expr.tokens, Expr.words, punctWord]

theorem enclose_params_flatten (ps : List Param) :
    (enclose "(" ")" (ps.map Param.words)).flatten =
      .punct "(" :: (joined "," (ps.map fun p => p.words.flatten) ++ [.punct ")"]) := by
  simp [enclose, punctWord, separated_flatten, List.map_map, Function.comp_def]

theorem Property.tokens_keyValue (k : PropKey) (v : Expr) :
    (Property.keyValue sp k v).tokens = k.words.flatten ++ .punct ":" :: v.tokens := by
  simp [Property.tokens, Property.words, Expr.tokens, punctWord]

end

/-! ### Arrow functions -/

/-- The token after a name at the start of an expression: not `,`, `:` or
`)`, which `arrowStart` looks for after a `(` and a name. -/
def secondOK (k : TokenKind) : Bool :=
  k != .punct "," && k != .punct ":" && k != .punct ")"

theorem secondOK_append {a b : List TokenKind} {c : TokenKind} (hne : a ≠ [])
    (ha : ∀ n k r, a = .ident n :: k :: r → secondOK k = true) (hc : secondOK c = true) :
    ∀ n k r, a ++ c :: b = .ident n :: k :: r → secondOK k = true := by
  intro n k r h
  match a, hne, h with
  | [x], _, h => simp at h; obtain ⟨_, rfl, _⟩ := h; exact hc
  | x :: y :: a', _, h => simp at h; obtain ⟨rfl, rfl, _⟩ := h; exact ha n y _ rfl

theorem secondOK_binOp (op : BinOp) :
    ∃ k ks, symbol op.symbol = k :: ks ∧ secondOK k = true ∧ k ≠ .punct "=>" := by
  cases op <;> simp [BinOp.symbol, symbol, Lex.reservedWords, punctWord, keywordWord, secondOK]

theorem secondOK_assignOp (op : AssignOp) :
    ∃ k ks, symbol op.symbol = k :: ks ∧ secondOK k = true ∧ k ≠ .punct "=>" := by
  cases op <;> simp [AssignOp.symbol, symbol, Lex.reservedWords, punctWord, secondOK]

theorem unary_notIdent (op : UnaryOp) : ∃ k ks, symbol op.symbol = k :: ks ∧ (∀ n, k ≠ .ident n) ∧
    k ≠ .punct "(" := by
  cases op <;> simp [UnaryOp.symbol, symbol, Lex.reservedWords, punctWord, keywordWord]

/-- After a name at the start of an expression comes an operator, a `.`, a `[`
or a `(`, or nothing. -/
theorem Expr.second_ok : ∀ e : Expr, ∀ n k r, e.tokens = .ident n :: k :: r → secondOK k = true
  | .ident .., _, _, _, h => by simp [Expr.tokens, Expr.words, identWord] at h
  | .number .., _, _, _, h | .bigint .., _, _, _, h | .string .., _, _, _, h | .null _, _, _, _, h => by
    simp [Expr.tokens, Expr.words, keywordWord] at h
  | .bool _ b, _, _, _, h => by cases b <;> simp [Expr.tokens, Expr.words, keywordWord] at h
  | .array .., _, _, _, h => by simp [Expr.tokens_array] at h
  | .object .., _, _, _, h => by simp [Expr.tokens_object] at h
  | .paren .., _, _, _, h => by simp [Expr.tokens_paren] at h
  | .new .., _, _, _, h => by simp [Expr.tokens_new] at h
  | .arrow _ parens ps _, n, k, r, h => by
    rw [Expr.tokens_arrow] at h
    rcases arrowParams_cases parens ps with ⟨p, _, _, hp⟩ | hp
    · simp [hp, identWord] at h; rw [← h.2.1]; rfl
    · simp [hp, enclose, punctWord] at h
  | .unary _ op a, _, _, _, h => by
    obtain ⟨k, ks, hk, hn, _⟩ := unary_notIdent op
    rw [Expr.tokens_unary, hk] at h; simp at h; exact absurd h.1 (hn _)
  | .prefix _ op a, _, _, _, h => by cases op <;> simp [Expr.tokens_prefix, UpdateOp.symbol] at h
  | .member _ o nm, n, k, r, h => by
    rw [Expr.tokens_member] at h
    obtain ⟨x, hx, _⟩ := Expr.first o
    exact secondOK_append (by intro h'; simp [h'] at hx) (Expr.second_ok o) (by decide) n k r h
  | .optMember _ o nm, n, k, r, h => by
    rw [Expr.tokens_optMember] at h
    obtain ⟨x, hx, _⟩ := Expr.first o
    exact secondOK_append (by intro h'; simp [h'] at hx) (Expr.second_ok o) (by decide) n k r h
  | .index _ o i, n, k, r, h => by
    simp only [Expr.tokens_index, List.append_assoc, List.cons_append] at h
    obtain ⟨x, hx, _⟩ := Expr.first o
    exact secondOK_append (c := .punct "[") (by intro h'; simp [h'] at hx) (Expr.second_ok o) (by decide) n k r h
  | .call _ c as, n, k, r, h => by
    simp only [Expr.tokens_call, List.append_assoc, List.cons_append] at h
    obtain ⟨x, hx, _⟩ := Expr.first c
    exact secondOK_append (c := .punct "(") (by intro h'; simp [h'] at hx) (Expr.second_ok c) (by decide) n k r h
  | .postfix _ op a, n, k, r, h => by
    rw [Expr.tokens_postfix] at h
    obtain ⟨x, hx, _⟩ := Expr.first a
    exact secondOK_append (by intro h'; simp [h'] at hx) (Expr.second_ok a) (by cases op <;> decide) n k r h
  | .binary _ op l rr, n, k, r, h => by
    rw [Expr.tokens_binary] at h
    obtain ⟨x, hx, _⟩ := Expr.first l
    obtain ⟨c, cs, hc, hck, _⟩ := secondOK_binOp op
    rw [hc] at h
    exact secondOK_append (by intro h'; simp [h'] at hx) (Expr.second_ok l) hck n k r (by simpa using h)
  | .asConst _ l, n, k, r, h => by
    rw [Expr.tokens_asConst] at h
    obtain ⟨x, hx, _⟩ := Expr.first l
    exact secondOK_append (by intro h'; simp [h'] at hx) (Expr.second_ok l) (by decide) n k r h
  | .satisfies _ l t, n, k, r, h => by
    rw [Expr.tokens_satisfies] at h
    obtain ⟨x, hx, _⟩ := Expr.first l
    exact secondOK_append (by intro h'; simp [h'] at hx) (Expr.second_ok l) (by decide) n k r h
  | .cond _ t a b, n, k, r, h => by
    simp only [Expr.tokens_cond, List.append_assoc, List.cons_append] at h
    obtain ⟨x, hx, _⟩ := Expr.first t
    exact secondOK_append (c := .punct "?") (by intro h'; simp [h'] at hx) (Expr.second_ok t) (by decide) n k r h
  | .assign _ op t v, n, k, r, h => by
    rw [Expr.tokens_assign] at h
    obtain ⟨x, hx, _⟩ := Expr.first t
    obtain ⟨c, cs, hc, hck, _⟩ := secondOK_assignOp op
    rw [hc] at h
    exact secondOK_append (by intro h'; simp [h'] at hx) (Expr.second_ok t) hck n k r (by simpa using h)

/-- An arrow function starts the tokens of `e`, at the end of the chain of
left operands, callees and objects that the tokens of `e` start with. -/
def Expr.leftArrow : Expr → Bool
  | .arrow .. => true
  | .member _ o _ | .optMember _ o _ | .index _ o _ | .call _ o _ | .postfix _ _ o | .binary _ _ o _
  | .cond _ o _ _ | .assign _ _ o _ | .asConst _ o | .satisfies _ o _ => o.leftArrow
  | _ => false

theorem arrowStart_cons {k : TokenKind} (hk : ∀ n, k ≠ .ident n) (hp : k ≠ .punct "(") (ks : List TokenKind) :
    Parse.arrowStart (k :: ks) = false := by
  cases ks with
  | nil => rfl
  | cons b ks =>
    cases k <;> simp_all [Parse.arrowStart]

theorem arrowStart_append {a b : List TokenKind} {c : TokenKind}
    (ha : ∀ after : List TokenKind, after.head? ≠ some (.punct "=>") → Parse.arrowStart (a ++ after) = false)
    (hc : c ≠ .punct "=>") : Parse.arrowStart (a ++ c :: b) = false :=
  ha _ (by simpa using hc)

/-- `arrowStart` finds no arrow function at an expression whose tokens start
with none, when no `=>` follows it. -/
theorem Expr.arrowStart_false : ∀ e : Expr, e.leftArrow = false → ∀ after : List TokenKind,
    after.head? ≠ some (.punct "=>") → Parse.arrowStart (e.tokens ++ after) = false
  | .ident _ n, _, after, ha => by
    cases after with
    | nil => rfl
    | cons b after => simp_all [Expr.tokens, Expr.words, identWord, Parse.arrowStart]
  | .number .., _, after, _ | .bigint .., _, after, _ | .string .., _, after, _ | .null _, _, after, _ =>
    arrowStart_cons (by simp) (by simp) _
  | .bool _ b, _, after, _ => by cases b <;> exact arrowStart_cons (by simp) (by simp) _
  | .array .., _, after, _ => by rw [Expr.tokens_array]; exact arrowStart_cons (by simp) (by simp) _
  | .object .., _, after, _ => by rw [Expr.tokens_object]; exact arrowStart_cons (by simp) (by simp) _
  | .new .., _, after, _ => by
    rw [Expr.tokens_new, List.cons_append]; exact arrowStart_cons (by simp) (by simp) _
  | .spread _ e, _, after, _ => by
    simp only [Expr.tokens, Expr.words, punctWord, List.flatten_cons, List.cons_append, List.nil_append]
    exact arrowStart_cons (by simp) (by simp) _
  | .unary _ op a, _, after, _ => by
    obtain ⟨k, ks, hk, hn, hp⟩ := unary_notIdent op
    rw [Expr.tokens_unary, hk]; exact arrowStart_cons hn hp _
  | .prefix _ op a, _, after, _ => by
    cases op <;> rw [Expr.tokens_prefix] <;> exact arrowStart_cons (by simp [UpdateOp.symbol]) (by simp [UpdateOp.symbol]) _
  | .arrow .., h, _, _ => by simp [Expr.leftArrow] at h
  | .paren _ i, _, after, ha => by
    rw [Expr.tokens_paren]
    obtain ⟨k, hk, hks⟩ := Expr.first i
    obtain ⟨r, hr⟩ : ∃ r, i.tokens = k :: r := by
      cases h : i.tokens with
      | nil => simp [h] at hk
      | cons x r => simp [h] at hk; exact ⟨r, by rw [hk]⟩
    have hk' : k ≠ .punct ")" := by intro h; rw [h] at hks; simp [startsExpr] at hks
    rw [hr]
    by_cases hid : ∃ n, k = .ident n
    · obtain ⟨n, rfl⟩ := hid
      cases r with
      | nil => cases after with
        | nil => simp [Parse.arrowStart]
        | cons d after => simp_all [Parse.arrowStart]
      | cons c r =>
        have hc := Expr.second_ok i n c r hr
        simp [secondOK] at hc
        simp [Parse.arrowStart, hc.1.1, hc.1.2, hc.2]
    · have hid' : ∀ n, k ≠ .ident n := fun n h => hid ⟨n, h⟩
      cases k <;> simp_all [Parse.arrowStart]
  | .member _ o nm, h, after, _ => by
    rw [Expr.tokens_member, List.append_assoc]
    exact arrowStart_append (Expr.arrowStart_false o (by simpa [Expr.leftArrow] using h)) (by simp)
  | .optMember _ o nm, h, after, _ => by
    rw [Expr.tokens_optMember, List.append_assoc]
    exact arrowStart_append (Expr.arrowStart_false o (by simpa [Expr.leftArrow] using h)) (by simp)
  | .index _ o i, h, after, _ => by
    simp only [Expr.tokens_index, List.append_assoc, List.cons_append]
    exact arrowStart_append (Expr.arrowStart_false o (by simpa [Expr.leftArrow] using h)) (by simp)
  | .call _ c as, h, after, _ => by
    simp only [Expr.tokens_call, List.append_assoc, List.cons_append]
    exact arrowStart_append (Expr.arrowStart_false c (by simpa [Expr.leftArrow] using h)) (by simp)
  | .postfix _ op a, h, after, _ => by
    rw [Expr.tokens_postfix, List.append_assoc]
    exact arrowStart_append (Expr.arrowStart_false a (by simpa [Expr.leftArrow] using h))
      (by cases op <;> simp [UpdateOp.symbol])
  | .binary _ op l r, h, after, _ => by
    rw [Expr.tokens_binary]
    obtain ⟨c, cs, hc, _, hck⟩ := secondOK_binOp op
    rw [hc]
    simpa using arrowStart_append (b := cs ++ r.tokens ++ after)
      (Expr.arrowStart_false l (by simpa [Expr.leftArrow] using h)) hck
  | .asConst _ l, h, after, _ => by
    rw [Expr.tokens_asConst, List.append_assoc]
    exact arrowStart_append (Expr.arrowStart_false l (by simpa [Expr.leftArrow] using h)) (by simp)
  | .satisfies _ l t, h, after, _ => by
    rw [Expr.tokens_satisfies, List.append_assoc]
    exact arrowStart_append (Expr.arrowStart_false l (by simpa [Expr.leftArrow] using h)) (by simp)
  | .cond _ t a b, h, after, _ => by
    simp only [Expr.tokens_cond, List.append_assoc, List.cons_append]
    exact arrowStart_append (Expr.arrowStart_false t (by simpa [Expr.leftArrow] using h)) (by simp)
  | .assign _ op t v, h, after, _ => by
    rw [Expr.tokens_assign]
    obtain ⟨c, cs, hc, _, hck⟩ := secondOK_assignOp op
    rw [hc]
    simpa using arrowStart_append (b := cs ++ v.tokens ++ after)
      (Expr.arrowStart_false t (by simpa [Expr.leftArrow] using h)) hck

/-- Below the level of assignments, no well-formed expression starts with an
arrow function. -/
theorem Expr.leftArrow_wf {T : Edition} : ∀ (e : Expr) (level : Level), e.wfAt T level = true →
    level ≠ .assign → e.leftArrow = false
  | .arrow .., level, h, hl => by cases level <;> simp_all [Expr.wfAt]
  | .member _ o _, level, h, _ | .index _ o _, level, h, _ | .call _ o _, level, h, _ => by
    have : o.wfAt T .lhs = true := by cases level <;> simp_all [Expr.wfAt]
    simpa [Expr.leftArrow] using Expr.leftArrow_wf o .lhs this (by simp)
  | .optMember _ o _, level, h, _ => by
    have : o.wfAt T .lhs = true := by cases level <;> simp_all [Expr.wfAt]
    simpa [Expr.leftArrow] using Expr.leftArrow_wf o .lhs this (by simp)
  | .postfix _ _ o, level, h, _ => by
    have : o.wfAt T .lhs = true := by cases level <;> simp_all [Expr.wfAt]
    simpa [Expr.leftArrow] using Expr.leftArrow_wf o .lhs this (by simp)
  | .binary _ _ o _, level, h, hl => by
    have : ∃ m, o.wfAt T (.bin m) = true := by
      cases level with
      | assign => exact absurd rfl hl
      | cond => simp only [Expr.wfAt, Bool.and_eq_true] at h; exact ⟨0, h.1.1.1.1.2⟩
      | bin m => simp only [Expr.wfAt, Bool.and_eq_true] at h; exact ⟨m, h.1.1.1.1.2⟩
      | _ => simp [Expr.wfAt] at h
    obtain ⟨m, hm⟩ := this
    simpa [Expr.leftArrow] using Expr.leftArrow_wf o (.bin m) hm (by simp)
  | .asConst _ o, level, h, hl => by
    have : ∃ m, o.wfAt T (.bin m) = true := by
      cases level with
      | assign => exact absurd rfl hl
      | cond => simp only [Expr.wfAt, Bool.and_eq_true] at h; exact ⟨0, h.1.2⟩
      | bin m => simp only [Expr.wfAt, Bool.and_eq_true] at h; exact ⟨m, h.1.2⟩
      | _ => simp [Expr.wfAt] at h
    obtain ⟨m, hm⟩ := this
    simpa [Expr.leftArrow] using Expr.leftArrow_wf o (.bin m) hm (by simp)
  | .satisfies _ o _, level, h, hl => by
    have : ∃ m, o.wfAt T (.bin m) = true := by
      cases level with
      | assign => exact absurd rfl hl
      | cond => simp only [Expr.wfAt, Bool.and_eq_true] at h; exact ⟨0, h.1.1.2⟩
      | bin m => simp only [Expr.wfAt, Bool.and_eq_true] at h; exact ⟨m, h.1.1.2⟩
      | _ => simp [Expr.wfAt] at h
    obtain ⟨m, hm⟩ := this
    simpa [Expr.leftArrow] using Expr.leftArrow_wf o (.bin m) hm (by simp)
  | .cond _ o _ _, level, h, hl => by
    have : o.wfAt T (.bin 0) = true := by
      cases level with
      | assign => exact absurd rfl hl
      | cond => simp [Expr.wfAt] at h; exact h.1.1.1
      | _ => simp [Expr.wfAt] at h
    simpa [Expr.leftArrow] using Expr.leftArrow_wf o (.bin 0) this (by simp)
  | .assign .., level, h, hl => by cases level <;> simp_all [Expr.wfAt]
  | .ident .., _, _, _ | .number .., _, _, _ | .bigint .., _, _, _ | .string .., _, _, _ | .bool .., _, _, _
  | .null _, _, _, _ | .array .., _, _, _ | .object .., _, _, _ | .paren .., _, _, _ | .unary .., _, _, _
  | .prefix .., _, _, _ | .new .., _, _, _ | .spread .., _, _, _ => by simp [Expr.leftArrow]

/-- An expression at the level of assignments that is not an arrow function
starts with none. -/
theorem Expr.leftArrow_assign {T : Edition} {e : Expr} (he : e.wfAt T .assign = true)
    (hna : ∀ sp p ps b, e ≠ .arrow sp p ps b) : e.leftArrow = false := by
  by_cases hasg : ∃ sp op t v, e = .assign sp op t v
  · obtain ⟨sp, op, t, v, rfl⟩ := hasg
    simp [Expr.wfAt] at he
    simpa [Expr.leftArrow] using Expr.leftArrow_wf t .cond he.1.1.1 (by simp)
  · have hne : ∀ sp op t v, e ≠ .assign sp op t v := fun sp op t v h' => hasg ⟨sp, op, t, v, h'⟩
    exact Expr.leftArrow_wf e .cond (by rw [← wfAt_assign_eq hne hna]; exact he) (by simp)

/-- `arrowStart` finds every arrow function that the printer writes. -/
theorem arrowStart_arrow (sp : Span) (parens : Bool) (ps : List Param) (b : Expr) (after : List TokenKind)
    (hopt : ∀ p ∈ ps, p.optional = false) :
    Parse.arrowStart ((Expr.arrow sp parens ps b).tokens ++ after) = true := by
  rw [Expr.tokens_arrow]
  rcases arrowParams_cases parens ps with ⟨p, _, _, hp⟩ | hp
  · simp [hp, identWord, Parse.arrowStart]
  rw [hp, enclose_params_flatten]
  match ps, hopt with
  | [], _ => simp [Parse.arrowStart, joined]
  | [⟨_, n, o, none⟩], h =>
    obtain rfl : o = false := h _ List.mem_cons_self
    simp [Parse.arrowStart, joined, Param.words, optionalMark, typeAnnotation, identWord]
  | [⟨_, n, o, some t⟩], h =>
    obtain rfl : o = false := h _ List.mem_cons_self
    simp [Parse.arrowStart, joined, Param.words, optionalMark, typeAnnotation, identWord, punctWord]
  | ⟨_, n, o, none⟩ :: q :: qs, h =>
    obtain rfl : o = false := h _ List.mem_cons_self
    simp [Parse.arrowStart, joined, Param.words, optionalMark, typeAnnotation, identWord]
  | ⟨_, n, o, some t⟩ :: q :: qs, h =>
    obtain rfl : o = false := h _ List.mem_cons_self
    simp [Parse.arrowStart, joined, Param.words, optionalMark, typeAnnotation, identWord, punctWord]

theorem arrowStart_take : ∀ ks : List TokenKind, Parse.arrowStart (ks.take 4) = Parse.arrowStart ks
  | [] | [_] | [_, _] | [_, _, _] | [_, _, _, _] => rfl
  | a :: b :: c :: d :: e :: ks => by simp [Parse.arrowStart]

theorem Parse.startsArrow_eq (s : ParseState) :
    Parse.startsArrow s = .ok (Parse.arrowStart (s.rest.map (·.kind))) s := by
  have : Parse.startsArrow s = .ok (Parse.arrowStart ((s.rest.take 4).map (·.kind))) s := rfl
  rw [this, List.map_take, arrowStart_take]

/-- `( params )`, which `parseArrowParams` reads. -/
theorem parseArrowParams_reads {T : Edition} (ps : List Param)
    (hps : ∀ p ∈ ps, p.wf = true ∧ (!p.optional) = true)
    (s : ParseState) (lp rp : Token) (its rest : List Token) (hT : s.target = T)
    (hs : s.rest = lp :: (its ++ rp :: rest)) (hl : s.left = s.rest.length) (hlp : lp.kind = .punct "(")
    (hrp : rp.kind = .punct ")") (ht : Touching its (separated "," (ps.map Param.words)))
    (hn : ∀ y ∈ its, NoBreak y) (hr : rest ≠ []) :
    ∃ ps' s', Parse.parseArrowParams s = .ok ps' s' ∧ ps'.map Param.erase = ps.map Param.erase ∧
      Leaves s s' rest := by
  let s₁ : ParseState := { s with rest := its ++ rp :: rest, left := s.left - 1, lastStop := lp.span.stop }
  have hl₁ : s₁.left = s₁.rest.length := by simp [s₁, hl, hs]
  obtain ⟨res, s₂, hit, hes, hL₂⟩ := params_reads (ok := false) ps (fun p hp => (hps p hp).1)
    (fun p hp h => by have := (hps p hp).2; simp [h] at this) s₁ its rest rp hT rfl hrp hl₁ ht hn
  have hs₂ : s₂.rest = rp :: rest := hL₂.rest_eq
  refine ⟨res.toList, { s₂ with rest := rest, left := s₂.left - 1, lastStop := rp.span.stop }, ?_, hes,
    leaves_trans (leaves_advance hs hl) (leaves_trans hL₂ (leaves_advance hs₂ (by rw [hL₂.left_eq, hs₂])))⟩
  simp only [Parse.parseArrowParams]
  rw [Parse.bind_eq (Parse.peek_eq hs)]
  simp only [Token.isPunct, hlp, beq_self_eq_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rw [Parse.pure_bind, Parse.bind_eq (Parse.discard_eq (Parse.advance_cons hs (by simp))), Parse.bind_eq (Parse.budget_eq _),
    Parse.bind_eq hit, Parse.bind_eq (Parse.expectPunct_ok hs₂ hr hrp)]
  rfl

/-- `parseArrow`, after `parseArrowParams` read the parameters: `=>` and the
body. -/
theorem parseArrow_ok {T : Edition} {g : Nat} {b : Expr} {s s₁ : ParseState} {first ar : Token}
    {r bts rest : List Token} {ps' : List Param}
    (hs : s.rest = first :: r) (hpp : Parse.parseArrowParams s = .ok ps' s₁)
    (hbrace : notFirst (.punct "{") b.tokens = true) (hb : ReadsE T (Parse.parseAssign g) b EndsAssign)
    (hT : s₁.target = T) (hs₁ : s₁.rest = ar :: (bts ++ rest)) (hl₁ : s₁.left = s₁.rest.length)
    (har : ar.kind = .punct "=>") (har' : ar.newlineBefore = false) (hbt : Touching bts b.words)
    (hn : ∀ y ∈ bts, NoBreak y) (hr : rest ≠ []) (hends : EndsAssign rest)
    (ha : b.afterOK (rest.map (·.kind)) = true) :
    ∃ b' s₃, Parse.parseArrow (g + 1) s =
        .ok (.arrow ⟨first.span.start, s₃.lastStop⟩ (first.isPunct "(") ps' b') s₃ ∧
      b'.erase = b.erase ∧ Leaves s₁ s₃ rest := by
  obtain ⟨u, bts', rfl, _⟩ := Touching.head hbt
  have hu : u.kind ≠ .punct "{" := by
    have hk := hbt.kinds
    simp only [List.map_cons] at hk
    simp only [notFirst, Expr.tokens, ← hk, List.head?_cons, bne_iff_ne, ne_eq, Option.some.injEq] at hbrace
    exact hbrace
  let s₂ : ParseState := { s₁ with rest := u :: bts' ++ rest, left := s₁.left - 1, lastStop := ar.span.stop }
  have hl₂ : s₂.left = s₂.rest.length := by simp [s₂, hl₁, hs₁]
  obtain ⟨b', s₃, hpb, heb, hL₃⟩ := hb s₂ (u :: bts') rest hT rfl hl₂ hbt
    (fun y hy => hn y (by simp only [List.tail_cons] at hy; simp [hy])) hr hends ha
  have hc : ar.kind ≠ .punct ":" := by rw [har]; exact punct_ne (by decide)
  refine ⟨b', s₃, ?_, heb, leaves_trans (leaves_advance hs₁ hl₁) hL₃⟩
  simp only [Parse.parseArrow]
  rw [Parse.bind_eq (Parse.peek_eq hs), Parse.bind_eq hpp, Parse.bind_eq (Parse.peek_eq hs₁)]
  rw [Parse.ite_guard (fun h => by simp [Token.isPunct, hc] at h)]
  rw [Parse.ite_guard (fun h => by simp [Token.isPunct, har] at h)]
  rw [Parse.bind_eq (Parse.expectPunct_ok hs₁ (by simp) har)]
  rw [Parse.ite_guard (fun h => by simp [har'] at h)]
  rw [Parse.bind_eq (Parse.peek_eq (s := s₂) (t := u) (r := bts' ++ rest) (by simp [s₂]))]
  rw [Parse.ite_guard (fun h => by simp [Token.isPunct, hu] at h)]
  rw [Parse.bind_eq hpb, Parse.bind_eq (Parse.spanFrom_eq _ _)]
  rfl

/-- An arrow function, which `parseArrow` reads when `parseAssign` reads its
body. -/
theorem parseArrow_reads {T : Edition} (g : Nat) (sp : Span) (parens : Bool) (ps : List Param) (b : Expr)
    (hshape : (parens || bareParam ps) = true) (hps : ∀ p ∈ ps, p.wf = true ∧ (!p.optional) = true)
    (hbrace : notFirst (.punct "{") b.tokens = true)
    (hb : ReadsE T (Parse.parseAssign g) b EndsAssign) :
    ReadsE T (Parse.parseArrow (g + 1)) (.arrow sp parens ps b) EndsAssign := by
  intro s ts rest hT hs hl ht hn hr hends ha
  simp only [Expr.afterOK] at ha
  simp only [Expr.words] at ht
  obtain ⟨pts, more, rfl, hpts, hmore⟩ := Touching.append_split ht
  obtain ⟨ar, bts, rfl, har, hbt⟩ := Touching.cons_one (by simpa [punctWord] using hmore)
  rcases arrowParams_cases parens ps with ⟨p, rfl, rfl, hp⟩ | hp
  · -- One name, without parentheses.
    obtain ⟨psp, n, o, ty⟩ := p
    cases ty with
    | some _ => simp [bareParam] at hshape
    | none =>
    obtain rfl : o = false := by simpa using (hps ⟨psp, n, o, none⟩ (by simp)).2
    have hn' : n ∉ Parse.refusedNames := by simpa [Param.wf, exprName] using (hps ⟨psp, n, false, none⟩ (by simp)).1
    rw [hp] at hpts
    obtain ⟨nm, ts₁, rfl, hnm, h₁⟩ := Touching.cons_one (by simpa [identWord] using hpts)
    simp [Touching] at h₁; subst h₁
    have hs' : s.rest = nm :: ar :: (bts ++ rest) := by rw [hs]; simp
    have har' : ar.newlineBefore = false := noBreak_of har (by decide) (hn ar (by simp))
    let s₁ := past s nm (ar :: (bts ++ rest))
    have hl₁ : s₁.left = s₁.rest.length := by simp [s₁, hl, hs']
    have hnp : nm.isPunct "(" = false := by simp [Token.isPunct, hnm]
    have hpa : Parse.parseArrowParams s = .ok [⟨nm.span, n, false, none⟩] s₁ := by
      simp only [Parse.parseArrowParams]
      rw [Parse.bind_eq (Parse.peek_eq hs')]
      simp only [hnp, Bool.not_false, ↓reduceIte]
      rw [Parse.bind_eq (readName_ok hs' hnm hn')]
      rfl
    obtain ⟨b', s₃, hpar, heb, hL₃⟩ := parseArrow_ok hs' hpa hbrace hb hT rfl hl₁ har har' hbt
      (fun y hy => hn y (by simp [hy])) hr hends ha
    rw [hnp] at hpar
    exact ⟨_, s₃, hpar, by simp [Expr.erase, Param.erase, heb], leaves_trans (leaves_advance hs' hl) hL₃⟩
  · -- The list in parentheses.
    have hparens : parens = true := by
      cases parens with
      | true => rfl
      | false =>
        simp only [Bool.false_or] at hshape
        match ps, hshape, hp with
        | [⟨_, _, _, none⟩], _, hp => simp [arrowParams, enclose, identWord, punctWord] at hp
        | [], h, _ => simp [bareParam] at h
        | [⟨_, _, _, some _⟩], h, _ => simp [bareParam] at h
        | _ :: _ :: _, h, _ => simp [bareParam] at h
    subst hparens
    rw [hp] at hpts
    obtain ⟨lp, its, rp, rfl, hlp, hits, hrp⟩ := Touching.enclosed (by simpa [enclose] using hpts)
    have hs' : s.rest = lp :: (its ++ rp :: (ar :: (bts ++ rest))) := by rw [hs]; simp
    have hn' : ∀ y ∈ its, NoBreak y := fun y hy => hn y (by simp [hy])
    have har' : ar.newlineBefore = false := noBreak_of har (by decide) (hn ar (by simp))
    obtain ⟨ps', s₁, hpp, hep, hL₁⟩ := parseArrowParams_reads ps hps s lp rp its (ar :: (bts ++ rest)) hT hs'
      hl hlp hrp hits hn' (by simp)
    have hs₁ : s₁.rest = ar :: (bts ++ rest) := hL₁.rest_eq
    have hl₁ : s₁.left = s₁.rest.length := by rw [hL₁.left_eq, hL₁.rest_eq]
    obtain ⟨b', s₃, hpar, heb, hL₃⟩ := parseArrow_ok hs' hpp hbrace hb (hL₁.target_eq.trans hT) hs₁ hl₁ har har'
      hbt (fun y hy => hn y (by simp [hy])) hr hends ha
    have hlp' : lp.isPunct "(" = true := by simp [Token.isPunct, hlp]
    rw [hlp'] at hpar
    exact ⟨_, s₃, hpar, by simp [Expr.erase, hep, heb], leaves_trans hL₁ hL₃⟩

theorem isSimpleTarget_cond {sp : Span} {t a b : Expr} : (Expr.cond sp t a b).isSimpleTarget = false := rfl

/-- An assignment, or what `parseConditional` reads. -/
theorem parseAssign_reads {T : Edition} (f : Nat) (e : Expr) (he : e.wfAt T .assign = true)
    (hC : ∀ x : Expr, x.height ≤ e.height → x.wfAt T .cond = true →
      ReadsE T (Parse.parseConditional f) x (Ends .cond x))
    (hA : ∀ x : Expr, x.height < e.height → x.wfAt T .assign = true →
      ReadsE T (Parse.parseAssign f) x EndsAssign)
    (hR : ∀ sp p ps b, e = .arrow sp p ps b → ReadsE T (Parse.parseArrow f) e EndsAssign) :
    ReadsE T (Parse.parseAssign (f + 1)) e EndsAssign := by
  intro s ts rest hT hs hl ht hn hr hends ha
  have hkinds : s.rest.map (·.kind) = e.tokens ++ rest.map (·.kind) := by
    rw [hs, List.map_append, ht.kinds]; rfl
  by_cases harr : ∃ sp p ps b, e = .arrow sp p ps b
  · obtain ⟨sp, p, ps, b, rfl⟩ := harr
    obtain ⟨e', s₁, hp, hee, hL⟩ := hR sp p ps b rfl s ts rest hT hs hl ht hn hr hends ha
    refine ⟨e', s₁, ?_, hee, hL⟩
    simp only [Parse.parseAssign]
    have hopt : ∀ q ∈ ps, q.optional = false := fun q hq => by
      simp only [Expr.wfAt, Bool.and_eq_true, List.all_eq_true] at he
      simpa using (he.1.1.2 q hq).2
    rw [Parse.bind_eq (Parse.startsArrow_eq s), hkinds, arrowStart_arrow _ _ _ _ _ hopt]
    simp only [↓reduceIte]
    rw [Parse.bind_eq hp]
    rfl
  have hna : ∀ sp p ps b, e ≠ .arrow sp p ps b := fun sp p ps b h' => harr ⟨sp, p, ps, b, h'⟩
  have hsa : Parse.startsArrow s = .ok false s := by
    rw [Parse.startsArrow_eq, hkinds, Expr.arrowStart_false e (Expr.leftArrow_assign he hna)]
    obtain ⟨u, r, rfl⟩ := List.exists_cons_of_ne_nil hr
    simpa using hends.2.1 u rfl
  obtain ⟨x, ts', rfl, _⟩ := Touching.head ht
  have hs' : s.rest = x :: (ts' ++ rest) := by simpa using hs
  by_cases hasg : ∃ sp op t v, e = .assign sp op t v
  · obtain ⟨sp, op, t, v, rfl⟩ := hasg
    simp only [Expr.wfAt, Bool.and_eq_true] at he
    obtain ⟨⟨⟨hwt, hsim⟩, hop⟩, hwv⟩ := he
    simp only [Expr.words] at ht
    obtain ⟨tts, more, hsplit, htt, hmore⟩ := Touching.append_split ht
    obtain ⟨a, vts, rfl, ha', hc, hvt⟩ := hmore
    obtain ⟨u, vts', rfl, hu⟩ := Touching.head hvt
    simp only [Expr.afterOK, Bool.and_eq_true] at ha
    obtain ⟨hta, hva⟩ := ha
    have hs₀ : s.rest = tts ++ (a ++ u :: (vts' ++ rest)) := by rw [hs, hsplit]; simp
    have hne : tts ≠ [] := by obtain ⟨_, _, rfl, _⟩ := Touching.head htt; simp
    have hnc : ∀ sp t' a' b', t ≠ .cond sp t' a' b' := by
      rintro sp t' a' b' rfl; simp [isSimpleTarget_cond] at hsim
    obtain ⟨t', s₁, hpt, het, hL₁⟩ := hC t (by simp [Expr.height]; omega) hwt s tts (a ++ u :: (vts' ++ rest)) hT
      hs₀ hl htt (fun y hy => hn y (tail_sub hsplit hne (.inl hy))) (by simp)
      (by rw [ends_cond_eq hnc]; exact endsCond_assignOp ha' (hc.chained ha') hu)
      (by rw [List.map_append, ha', ← List.cons_append, List.map_append, hvt.kinds]
          simpa [Expr.tokens, List.append_assoc] using hta)
    have hs₁ : s₁.rest = a ++ u :: (vts' ++ rest) := hL₁.rest_eq
    have hl₁ : s₁.left = s₁.rest.length := by rw [hL₁.left_eq, hL₁.rest_eq]
    obtain ⟨k, ks, hk, _, _, hkarrow⟩ := assignOp_head op
    obtain ⟨o, a', rfl, hok, _⟩ := List.map_eq_cons_iff.mp (ha'.trans hk)
    have hs₁' : s₁.rest = o :: (a' ++ u :: (vts' ++ rest)) := by simp [hs₁]
    obtain ⟨s₂, hsk, hLk⟩ := Parse.skip_ok (o :: a') hs₁ (by simp) hl₁
    have hl₂ : s₂.left = s₂.rest.length := by rw [hLk.left_eq, hLk.rest_eq]
    obtain ⟨v', s₃, hpv, hev, hL₃⟩ := hA v (by simp [Expr.height]; omega) hwv s₂ (u :: vts') rest
      (hLk.target_eq.trans (hL₁.target_eq.trans hT)) (by simpa using hLk.rest_eq) hl₂ hvt
      (fun y hy => hn y (tail_sub hsplit hne (.inr (by simp at hy ⊢; simp [hy])))) hr hends hva
    have hsim' : t'.isSimpleTarget = true := by rw [isSimpleTarget_of_erase het]; exact hsim
    have hT₁ : s₁.target = T := hL₁.target_eq.trans hT
    refine ⟨.assign ⟨x.span.start, s₃.lastStop⟩ op t' v', s₃, ?_, by simp [Expr.erase, het, hev],
      leaves_trans hL₁ (leaves_trans hLk hL₃)⟩
    simp only [Parse.parseAssign]
    rw [Parse.bind_eq hsa]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [Parse.pure_bind]
    rw [Parse.bind_eq (Parse.peek_eq hs'), Parse.bind_eq hpt, Parse.bind_eq (Parse.peek_eq hs₁')]
    rw [Parse.ite_guard (fun h => by simp [Token.isPunct, hok] at h; exact absurd h hkarrow)]
    rw [Parse.bind_eq (peekAssignOp_op hs₁ ha' (hc.chained ha') hu)]
    dsimp only
    rw [if_pos hsim', Parse.pure_bind]
    cases op <;> simp only [AssignOp.allowedIn] at hop <;> dsimp only <;>
      (first
        | rw [Parse.bind_eq (Parse.requireFeature_ok (by rw [hT₁]; exact hop))]
        | rw [Parse.pure_bind]) <;>
      rw [Parse.bind_eq hsk, Parse.bind_eq hpv, Parse.bind_eq (Parse.spanFrom_eq _ _)] <;> rfl
  · have hne : ∀ sp op t v, e ≠ .assign sp op t v := fun sp op t v h' => hasg ⟨sp, op, t, v, h'⟩
    have he' : e.wfAt T .cond = true := by rw [← wfAt_assign_eq hne hna]; exact he
    have hends' : Ends .cond e rest := by
      by_cases hc : ∃ sp t a b, e = .cond sp t a b
      · obtain ⟨sp, t, a, b, rfl⟩ := hc; exact hends
      · rw [ends_cond_eq (fun sp t a b h' => hc ⟨sp, t, a, b, h'⟩)]; exact hends.1
    obtain ⟨e', s₁, hp, hee, hL₁⟩ := hC e (Nat.le_refl _) he' s (x :: ts') rest hT hs hl ht hn hr hends' ha
    obtain ⟨u, r, rfl⟩ := List.exists_cons_of_ne_nil hr
    have hu : u.kind ≠ .punct "=>" := hends.2.1 u rfl
    have hpa := hends.2.2 s₁ hL₁.rest_eq
    refine ⟨e', s₁, ?_, hee, hL₁⟩
    simp only [Parse.parseAssign]
    rw [Parse.bind_eq hsa]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [Parse.pure_bind]
    rw [Parse.bind_eq (Parse.peek_eq hs'), Parse.bind_eq hp, Parse.bind_eq (Parse.peek_eq hL₁.rest_eq)]
    rw [Parse.ite_guard (fun h => by simp [Token.isPunct] at h; exact absurd h hu)]
    rw [Parse.bind_eq hpa]
    rfl

/-! ### Every expression -/

theorem Expr.height_le_heightOf {x : Expr} : ∀ {es : List Expr}, x ∈ es → x.height ≤ Expr.heightOf es
  | e :: es, h => by
    simp at h
    rcases h with rfl | h
    · simp [Expr.heightOf]; omega
    · have := Expr.height_le_heightOf h; simp [Expr.heightOf]; omega

theorem Property.height_le_heightOf {q : Property} : ∀ {ps : List Property}, q ∈ ps →
    q.height ≤ Property.heightOf ps
  | p :: ps, h => by
    simp at h
    rcases h with rfl | h
    · simp [Property.heightOf]; omega
    · have := Property.height_le_heightOf h; simp [Property.heightOf]; omega

theorem Expr.allWF_iff {T : Edition} : ∀ {es : List Expr}, Expr.allWF T es = true ↔ ∀ x ∈ es, x.elemWF T = true
  | [] => by simp [Expr.allWF]
  | e :: es => by simp [Expr.allWF, Expr.allWF_iff]

theorem Property.allWF_iff {T : Edition} : ∀ {ps : List Property},
    Property.allWF T ps = true ↔ ∀ q ∈ ps, q.wf T = true
  | [] => by simp [Property.allWF]
  | p :: ps => by simp [Property.allWF, Property.allWF_iff]

/-- A parser that reads one token of kind `k` reads every expression whose one
word is `[k]`. -/
theorem readsE_one {T : Edition} {p : ParseM Expr} {e : Expr} {k : TokenKind} {E : List Token → Prop}
    (hw : e.words = [[k]])
    (hp : ∀ s x u r, s.rest = x :: u :: r → x.kind = k →
      ∃ e', p s = .ok e' (past s x (u :: r)) ∧ e'.erase = e.erase) :
    ReadsE T p e E := by
  intro s ts rest _ hs hl ht _ hr _ _
  rw [hw] at ht
  obtain ⟨x, ts', rfl, hx, h'⟩ := Touching.cons_one ht
  simp [Touching] at h'; subst h'
  obtain ⟨u, r, rfl⟩ := List.exists_cons_of_ne_nil hr
  have hs' : s.rest = x :: u :: r := by simpa using hs
  obtain ⟨e', hpe, he⟩ := hp s x u r hs' hx
  exact ⟨e', _, hpe, he, leaves_advance hs' hl⟩

/-- `parsePrimary` reads `[`…`]` with `parseArrayLiteral`. -/
theorem parsePrimary_array {T : Edition} (f : Nat) (sp : Span) (es : List Expr)
    (h : ReadsE T (Parse.parseArrayLiteral f) (.array sp es) (fun _ => True)) :
    ReadsE T (Parse.parsePrimary (f + 1)) (.array sp es) (fun _ => True) := by
  intro s ts rest hT hs hl ht hn hr he ha
  obtain ⟨lp, its, rp, rfl, hlp, _, _⟩ := Touching.enclosed (by simpa [Expr.words, enclose] using ht)
  obtain ⟨e', s', hp, hee, hL⟩ := h s _ rest hT hs hl ht hn hr he ha
  refine ⟨e', s', ?_, hee, hL⟩
  simp only [Parse.parsePrimary]
  rw [Parse.bind_eq (Parse.peek_eq (by simpa using hs))]
  simp only [hlp]
  exact hp

/-- `parsePrimary` reads `new …` with `parseNew`. -/
theorem parsePrimary_new {T : Edition} (f : Nat) (sp : Span) (c : String) (targs : List TypeExpr)
    (args : List Expr) (h : ReadsE T (Parse.parseNew f) (.new sp c targs args) (fun _ => True)) :
    ReadsE T (Parse.parsePrimary (f + 1)) (.new sp c targs args) (fun _ => True) := by
  intro s ts rest hT hs hl ht hn hr he ha
  have ht' := ht
  rw [show (Expr.new sp c targs args).words = [.keyword "new"] :: _ from rfl] at ht'
  obtain ⟨nw, ts₁, rfl, hnw, _⟩ := Touching.cons_one ht'
  obtain ⟨e', s', hp, hee, hL⟩ := h s _ rest hT hs hl ht hn hr he ha
  refine ⟨e', s', ?_, hee, hL⟩
  simp only [Parse.parsePrimary]
  rw [Parse.bind_eq (Parse.peek_eq (by simpa using hs))]
  simp only [hnw]
  exact hp

/-- `parsePrimary` reads `{`…`}` with `parseObjectLiteral`. -/
theorem parsePrimary_object {T : Edition} (f : Nat) (sp : Span) (ps : List Property)
    (h : ReadsE T (Parse.parseObjectLiteral f) (.object sp ps) (fun _ => True)) :
    ReadsE T (Parse.parsePrimary (f + 1)) (.object sp ps) (fun _ => True) := by
  intro s ts rest hT hs hl ht hn hr he ha
  obtain ⟨lp, its, rp, rfl, hlp, _, _⟩ := Touching.enclosed (by simpa [Expr.words, enclose] using ht)
  obtain ⟨e', s', hp, hee, hL⟩ := h s _ rest hT hs hl ht hn hr he ha
  refine ⟨e', s', ?_, hee, hL⟩
  simp only [Parse.parsePrimary]
  rw [Parse.bind_eq (Parse.peek_eq (by simpa using hs))]
  simp only [hlp]
  exact hp


/-- Every primary expression, with the levels below it read with less fuel. -/
theorem primary_reads {T : Edition} (f : Nat) (IH : ∀ g ≤ f, AllRead T g) (e : Expr)
    (he : e.wfAt T .primary = true) (hn : need .primary e ≤ f + 1) :
    ReadsE T (Parse.parsePrimary (f + 1)) e (fun _ => True) := by
  cases e with
  | ident sp n =>
    have hn' : n ∉ Parse.refusedNames := by simpa [Expr.wfAt, exprName] using he
    exact readsE_one (k := .ident n) (by simp [Expr.words, identWord]) fun s x u r hs hx =>
      ⟨_, parsePrimary_ident f s x u r n hs hx hn', by simp [Expr.erase]⟩
  | number sp t =>
    exact readsE_one (k := .number t) (by simp [Expr.words]) fun s x u r hs hx =>
      ⟨_, parsePrimary_simple f s x u r (.number x.span t) hs (by simp [simpleExpr, hx]), by simp [Expr.erase]⟩
  | bigint sp t =>
    exact readsE_one (k := .bigint t) (by simp [Expr.words]) fun s x u r hs hx =>
      ⟨_, parsePrimary_simple f s x u r (.bigint x.span t) hs (by simp [simpleExpr, hx]), by simp [Expr.erase]⟩
  | string sp v =>
    exact readsE_one (k := .string v) (by simp [Expr.words]) fun s x u r hs hx =>
      ⟨_, parsePrimary_simple f s x u r (.string x.span v) hs (by simp [simpleExpr, hx]), by simp [Expr.erase]⟩
  | bool sp b =>
    cases b
    · exact readsE_one (k := .keyword "false") (by simp [Expr.words, keywordWord]) fun s x u r hs hx =>
        ⟨_, parsePrimary_simple f s x u r (.bool x.span false) hs (by simp [simpleExpr, hx]), by simp [Expr.erase]⟩
    · exact readsE_one (k := .keyword "true") (by simp [Expr.words, keywordWord]) fun s x u r hs hx =>
        ⟨_, parsePrimary_simple f s x u r (.bool x.span true) hs (by simp [simpleExpr, hx]), by simp [Expr.erase]⟩
  | null sp =>
    exact readsE_one (k := .keyword "null") (by simp [Expr.words, keywordWord]) fun s x u r hs hx =>
      ⟨_, parsePrimary_simple f s x u r (.null x.span) hs (by simp [simpleExpr, hx]), by simp [Expr.erase]⟩
  | paren sp inner =>
    simp only [Expr.wfAt] at he
    simp only [need, Level.cost, Expr.height] at hn
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    exact parsePrimary_paren (g + 1) sp inner (expression_reads g inner
      (IH g (by omega) .assign inner he (by simp only [need, Level.cost]; omega)))
  | array sp es =>
    simp only [Expr.wfAt] at he
    simp only [need, Level.cost, Expr.height] at hn
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    exact parsePrimary_array (g + 1) sp es (parseArrayLiteral_reads g sp es fun x hx =>
      parseElement_of (Expr.allWF_iff.mp he x hx) fun v hv hh =>
        IH g (by omega) .assign v hv
          (by have := Expr.height_le_heightOf hx; simp only [need, Level.cost]; omega))
  | object sp ps =>
    simp only [Expr.wfAt] at he
    simp only [need, Level.cost, Expr.height] at hn
    obtain ⟨h, rfl⟩ : ∃ h, f = h + 1 + 1 := ⟨f - 2, by omega⟩
    refine parsePrimary_object (h + 1 + 1) sp ps (parseObjectLiteral_reads (h + 1) sp ps fun q hq =>
      parseProperty_reads h q (Property.allWF_iff.mp he q hq) (fun sp' key v hqv => ?_) (fun sp' v hqv => ?_))
    all_goals
      subst hqv
      have hw := Property.allWF_iff.mp he _ hq
      have hh := Property.height_le_heightOf hq
      simp only [Property.wf, Bool.and_eq_true] at hw
      simp only [Property.height] at hh
      exact IH h (by omega) .assign v (by first | exact hw | exact hw.2) (by simp only [need, Level.cost]; omega)
  | new sp c ts as =>
    simp only [Expr.wfAt, Bool.and_eq_true] at he
    simp only [need, Level.cost, Expr.height] at hn
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 + 1 := ⟨f - 2, by omega⟩
    exact parsePrimary_new (g + 1 + 1) sp c ts as (parseNew_reads g sp c ts as he.1.1 he.1.2 fun x hx =>
      parseElement_of (Expr.allWF_iff.mp he.2 x hx) fun v hv hh =>
        IH g (by omega) .assign v hv
          (by have := Expr.height_le_heightOf hx; simp only [need, Level.cost]; omega))
  | _ => simp [Expr.wfAt] at he

/-- The step of the induction on fuel. -/
theorem allRead_succ {T : Edition} (f : Nat) (IH : ∀ g ≤ f, AllRead T g) : AllRead T (f + 1) := by
  intro level e he hn
  simp only [need] at hn
  cases level with
  | primary => exact primary_reads f IH e he hn
  | lhs =>
    simp only [Level.cost] at hn
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    exact parseLeftHandSide_reads (g + 1) e he
      (IH (g + 1) (Nat.le_refl _) .primary (lhsHead e) (wf_lhsHead e he)
        (by have := height_lhsHead e; simp only [need, Level.cost]; omega))
      (fun x hx hw => expression_reads g x (IH g (by omega) .assign x hw (by simp only [need, Level.cost]; omega)))
      (fun args ha hw => parseArguments_reads g args fun x hx =>
        parseElement_of (Expr.allWF_iff.mp hw x hx) fun v hv hh =>
          IH g (by omega) .assign v hv
            (by have := Expr.height_le_heightOf hx; simp only [need, Level.cost]; omega))
  | «postfix» =>
    simp only [Level.cost] at hn
    exact parsePostfix_reads f e he fun x hx hw =>
      IH f (Nat.le_refl _) .lhs x hw (by simp only [need, Level.cost]; omega)
  | unary =>
    simp only [Level.cost] at hn
    exact parseUnary_reads f e he
      (fun x hx hw => IH f (Nat.le_refl _) .unary x hw (by simp only [need, Level.cost]; omega))
      (fun x hx hw => IH f (Nat.le_refl _) .lhs x hw (by simp only [need, Level.cost]; omega))
      (fun hw => IH f (Nat.le_refl _) .postfix e hw (by simp only [need, Level.cost]; omega))
  | bin m =>
    simp only [Level.cost] at hn
    exact parseBinary_reads f m e he
      (IH f (Nat.le_refl _) .unary (binHead e) (wf_binHead e he)
        (by have := height_binHead e; simp only [need, Level.cost]; omega))
      (fun x k hx hw => IH f (Nat.le_refl _) (.bin k) x hw (by simp only [need, Level.cost]; omega))
  | cond =>
    simp only [Level.cost] at hn
    exact parseConditional_reads f e he
      (fun x hx hw => IH f (Nat.le_refl _) (.bin 0) x hw (by simp only [need, Level.cost]; omega))
      (fun x hx hw => IH f (Nat.le_refl _) .assign x hw (by simp only [need, Level.cost]; omega))
  | assign =>
    simp only [Level.cost] at hn
    exact parseAssign_reads f e he
      (fun x hx hw => IH f (Nat.le_refl _) .cond x hw (by simp only [need, Level.cost]; omega))
      (fun x hx hw => IH f (Nat.le_refl _) .assign x hw (by simp only [need, Level.cost]; omega))
      (fun sp p ps b h => by
        subst h
        simp only [Expr.height] at hn
        obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
        simp only [Expr.wfAt, Bool.and_eq_true, List.all_eq_true] at he
        exact parseArrow_reads g sp p ps b he.1.1.1 he.1.1.2 he.2
          (IH g (by omega) .assign b he.1.2 (by simp only [need, Level.cost]; omega)))

theorem exprs_read_le (T : Edition) : ∀ f, ∀ g ≤ f, AllRead T g := by
  intro f
  induction f with
  | zero =>
    intro g hg level e _ hn
    have : g = 0 := by omega
    subst this
    cases level <;> simp only [need, Level.cost] at hn <;> omega
  | succ f ih =>
    intro g hg
    by_cases h : g ≤ f
    · exact ih g h
    · have : g = f + 1 := by omega
      subst this
      exact allRead_succ f ih

/-- The parser's round trip for expressions, on tokens: with fuel `f`, the
function for each level reads the printed tokens of every expression that is
well formed there and needs at most `f`, as that expression apart from spans,
whatever follows that ends the level. -/
theorem exprs_read (T : Edition) (f : Nat) : AllRead T f := exprs_read_le T f f (Nat.le_refl _)

/-! ### What follows an expression -/

/-- A `>` comes in `ks`. -/
def hasGreater (ks : List TokenKind) : Bool := ks.contains (.punct ">")

/-- The scan of `closesKinds` passes over `ks` at every depth: `ks` closes no
group that it does not open, and has no `;` and no end of file. -/
def Neutral (ks : List TokenKind) : Prop :=
  ∀ d a, closesKinds d (ks ++ a) = (hasGreater ks || closesKinds d a)

theorem Neutral.nil : Neutral [] := fun _ _ => by simp [hasGreater]

theorem Neutral.append {a b : List TokenKind} (ha : Neutral a) (hb : Neutral b) : Neutral (a ++ b) :=
  fun d x => by rw [List.append_assoc, ha, hb]; simp [hasGreater, Bool.or_assoc]

/-- A token other than a bracket, a `;` and the end of the file. -/
theorem Neutral.one {k : TokenKind} (h1 : k ∉ [.punct "(", .punct "[", .punct "{", .punct ")", .punct "]",
    .punct "}", .punct ";", .eof]) : Neutral [k] := by
  intro d a
  simp at h1
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h1
  by_cases hg : k = .punct ">"
  · subst hg; simp [closesKinds, hasGreater]
  · cases k with
    | punct p =>
      simp only [TokenKind.punct.injEq] at h1 h2 h3 h4 h5 h6 h7 hg
      have hg' : ">" ≠ p := fun e => hg e.symm
      simp [closesKinds, hasGreater, h1, h2, h3, h4, h5, h6, h7, hg, hg']
    | eof => exact absurd rfl h8
    | _ => simp [closesKinds, hasGreater]

/-- A group in brackets. -/
theorem Neutral.enclosed {o c : String} (ho : o ∈ ["(", "[", "{"]) (hc : c ∈ [")", "]", "}"])
    {ks : List TokenKind} (h : Neutral ks) : Neutral (.punct o :: (ks ++ [.punct c])) := by
  intro d a
  simp at ho hc
  have hopen : closesKinds d (.punct o :: (ks ++ .punct c :: a)) = closesKinds (d + 1) (ks ++ .punct c :: a) := by
    rcases ho with rfl | rfl | rfl <;> simp [closesKinds]
  have hclose : closesKinds (d + 1) (.punct c :: a) = closesKinds d a := by
    rcases hc with rfl | rfl | rfl <;> simp [closesKinds]
  simp only [List.cons_append, List.append_assoc, List.nil_append]
  rw [hopen, h, hclose]
  have h1 : ">" ≠ o := by rcases ho with rfl | rfl | rfl <;> decide
  have h2 : ">" ≠ c := by rcases hc with rfl | rfl | rfl <;> decide
  simp [hasGreater, h1, h2]


theorem Neutral.cons {k : TokenKind} {ks : List TokenKind} (hk : k ∉ [.punct "(", .punct "[", .punct "{",
    .punct ")", .punct "]", .punct "}", .punct ";", .eof]) (h : Neutral ks) : Neutral (k :: ks) :=
  Neutral.append (a := [k]) (Neutral.one hk) h

/-- Tokens none of which is a bracket, a `;` or the end of the file. -/
theorem Neutral.all : ∀ {ks : List TokenKind}, (∀ k ∈ ks, k ∉ [.punct "(", .punct "[", .punct "{",
    .punct ")", .punct "]", .punct "}", .punct ";", .eof]) → Neutral ks
  | [], _ => Neutral.nil
  | k :: ks, h => Neutral.cons (h k (by simp)) (Neutral.all fun x hx => h x (by simp [hx]))

theorem Neutral.join : ∀ {xs : List (List TokenKind)}, (∀ x ∈ xs, Neutral x) → Neutral (joined "," xs)
  | [], _ => Neutral.nil
  | [x], h => by simpa [joined] using h x (by simp)
  | x :: y :: xs, h => by
    show Neutral (x ++ .punct "," :: joined "," (y :: xs))
    exact Neutral.append (h x (by simp)) (Neutral.cons (by simp)
      (Neutral.join fun z hz => h z (by simp at hz ⊢; rcases hz with h' | h' <;> simp [h'])))

theorem neutral_binOp (op : BinOp) : Neutral (symbol op.symbol) := by
  apply Neutral.all
  cases op <;> simp [BinOp.symbol, symbol, Lex.reservedWords, punctWord, keywordWord]

theorem neutral_assignOp (op : AssignOp) : Neutral (symbol op.symbol) := by
  apply Neutral.all
  cases op <;> simp [AssignOp.symbol, symbol, Lex.reservedWords, punctWord]

theorem neutral_unaryOp (op : UnaryOp) : Neutral (symbol op.symbol) := by
  apply Neutral.all
  cases op <;> simp [UnaryOp.symbol, symbol, Lex.reservedWords, punctWord, keywordWord]

theorem neutral_updateOp (op : UpdateOp) : Neutral [.punct op.symbol] := by
  apply Neutral.all
  cases op <;> simp [UpdateOp.symbol]

theorem neutral_propertyName (n : String) : Neutral (propertyName n) := by
  apply Neutral.all
  unfold propertyName; split <;> simp [keywordWord, identWord]

theorem neutral_key (k : PropKey) : Neutral (k.words.flatten) := by
  cases k with
  | ident n => simpa [PropKey.words] using neutral_propertyName n
  | string v => exact Neutral.all (by simp [PropKey.words])
  | number t => exact Neutral.all (by simp [PropKey.words])

mutual

/-- The tokens of a type are neutral: its brackets match, and it has no `;`. -/
theorem TypeExpr.neutral : ∀ t : TypeExpr, Neutral t.tokens
  | .predicate _ _ target => by
    simpa [TypeExpr.tokens, TypeExpr.words, identWord] using
      Neutral.cons (k := .ident _) (by simp) (Neutral.cons (k := .ident "is") (by simp) (TypeExpr.neutral target))
  | .ref _ n [] => Neutral.all (by simp [TypeExpr.tokens, TypeExpr.words, identWord])
  | .ref sp n (a :: as) => by
    rw [tokens_ref sp n _ (by simp)]
    exact Neutral.cons (by simp) (Neutral.cons (by simp)
      (Neutral.append (Neutral.join (TypeExpr.neutralAll (a :: as))) (Neutral.one (by simp))))
  | .paren sp i => by
    rw [TypeExpr.tokens_paren]
    exact Neutral.enclosed (o := "(") (c := ")") (by simp) (by simp) (TypeExpr.neutral i)
  | .array sp e => by
    rw [TypeExpr.tokens_array]
    exact Neutral.append (TypeExpr.neutral e)
      (by simpa using Neutral.enclosed (o := "[") (c := "]") (by simp) (by simp) Neutral.nil)
  | .union _ [] => by simpa [TypeExpr.tokens, TypeExpr.words, separated, TypeExpr.wordsOf] using Neutral.nil
  | .union sp [m] => by rw [tokens_union_one]; exact Neutral.cons (by simp) (TypeExpr.neutral m)
  | .union sp (m₁ :: m₂ :: ms) => by
    rw [tokens_union]; exact Neutral.append (TypeExpr.neutral m₁) (TypeExpr.neutralBars (m₂ :: ms))
  | .keyword _ n => Neutral.all (by
      simp only [TypeExpr.tokens, TypeExpr.words]; split <;> simp [keywordWord, identWord])
  | .null _ => Neutral.all (by simp [TypeExpr.tokens, TypeExpr.words, keywordWord])
  | .literal _ l => Neutral.all (by
      cases l <;> simp [TypeExpr.tokens, TypeExpr.words, LitType.words, keywordWord])
  | .tuple sp false es => by
    rw [tokens_tuple]
    exact Neutral.enclosed (o := "[") (c := "]") (by simp) (by simp) (Neutral.join (TypeExpr.neutralAll es))
  | .tuple sp true es => by
    rw [tokens_readonly, tokens_tuple]
    exact Neutral.cons (by simp)
      (Neutral.enclosed (o := "[") (c := "]") (by simp) (by simp) (Neutral.join (TypeExpr.neutralAll es)))

theorem TypeExpr.neutralAll : ∀ ts : List TypeExpr, ∀ x ∈ ts.map TypeExpr.tokens, Neutral x
  | [], _, h => by simp at h
  | t :: ts, x, h => by
    simp at h
    rcases h with rfl | h
    · exact TypeExpr.neutral t
    · exact TypeExpr.neutralAll ts x (by simpa using h)

theorem TypeExpr.neutralBars : ∀ ts : List TypeExpr,
    Neutral (ts.map fun i => .punct "|" :: i.tokens).flatten
  | [] => Neutral.nil
  | t :: ts => by
    simp only [List.map_cons, List.flatten_cons]
    exact Neutral.append (Neutral.cons (by simp) (TypeExpr.neutral t)) (TypeExpr.neutralBars ts)

end

theorem Param.neutral (p : Param) : Neutral p.words.flatten := by
  obtain ⟨_, n, o, ty⟩ := p
  cases o <;> cases ty with
  | none => exact Neutral.all (by simp [Param.words, optionalMark, typeAnnotation, identWord, punctWord])
  | some t =>
    first
    | have := Neutral.cons (k := .ident n) (by simp) (Neutral.cons (k := .punct ":") (by simp) (TypeExpr.neutral t))
      simpa [Param.words, optionalMark, typeAnnotation, identWord, punctWord, TypeExpr.tokens] using this
    | have := Neutral.cons (k := .ident n) (by simp) (Neutral.cons (k := .punct "?") (by simp)
        (Neutral.cons (k := .punct ":") (by simp) (TypeExpr.neutral t)))
      simpa [Param.words, optionalMark, typeAnnotation, identWord, punctWord, TypeExpr.tokens] using this

mutual

/-- The tokens of an expression are neutral: its brackets match, and it has no
`;`. -/
theorem Expr.neutral : ∀ e : Expr, Neutral e.tokens
  | .ident _ n => Neutral.all (by simp [Expr.tokens, Expr.words, identWord])
  | .number .. | .bigint .. | .string .. | .null _ => Neutral.all (by simp [Expr.tokens, Expr.words, keywordWord])
  | .bool _ b => Neutral.all (by cases b <;> simp [Expr.tokens, Expr.words, keywordWord])
  | .array _ es => by
    have h := Neutral.enclosed (o := "[") (c := "]") (by simp) (by simp) (Neutral.join (Expr.neutralAll es))
    simpa [Expr.tokens, Expr.words, enclose, punctWord, separated_flatten, Expr.wordsOf_eq, List.map_map,
      Function.comp_def] using h
  | .object _ ps => by
    have h := Neutral.enclosed (o := "{") (c := "}") (by simp) (by simp) (Neutral.join (Property.neutralAll ps))
    simpa [Expr.tokens, Expr.words, enclose, punctWord, separated_flatten, Property.wordsOf_eq, List.map_map,
      Function.comp_def] using h
  | .paren _ i => by
    have h := Neutral.enclosed (o := "(") (c := ")") (by simp) (by simp) (Expr.neutral i)
    simpa [Expr.tokens, Expr.words, punctWord] using h
  | .new sp c ts as => by
    rw [Expr.tokens_new]
    exact Neutral.cons (by simp) (Neutral.append (TypeExpr.neutral (.ref sp c ts))
      (Neutral.enclosed (o := "(") (c := ")") (by simp) (by simp) (Neutral.join (Expr.neutralAll as))))
  | .member _ o n => by
    have h := Neutral.append (Expr.neutral o) (Neutral.cons (k := .punct ".") (by simp) (neutral_propertyName n))
    simpa [Expr.tokens, Expr.words, punctWord] using h
  | .optMember _ o n => by
    have h := Neutral.append (Expr.neutral o) (Neutral.cons (k := .punct "?.") (by simp) (neutral_propertyName n))
    simpa [Expr.tokens, Expr.words, punctWord] using h
  | .index _ o i => by
    have h := Neutral.append (Expr.neutral o)
      (Neutral.enclosed (o := "[") (c := "]") (by simp) (by simp) (Expr.neutral i))
    simpa [Expr.tokens, Expr.words, punctWord] using h
  | .call _ c as => by
    have h := Neutral.append (Expr.neutral c)
      (Neutral.enclosed (o := "(") (c := ")") (by simp) (by simp) (Neutral.join (Expr.neutralAll as)))
    simpa [Expr.tokens, Expr.words, enclose, punctWord, separated_flatten, Expr.wordsOf_eq, List.map_map,
      Function.comp_def] using h
  | .unary _ op a => by
    have h := Neutral.append (neutral_unaryOp op) (Expr.neutral a)
    simpa [Expr.tokens, Expr.words] using h
  | .prefix _ op a => by
    have h := Neutral.append (neutral_updateOp op) (Expr.neutral a)
    simpa [Expr.tokens, Expr.words, punctWord] using h
  | .postfix _ op a => by
    have h := Neutral.append (Expr.neutral a) (neutral_updateOp op)
    simpa [Expr.tokens, Expr.words, punctWord] using h
  | .binary _ op l r => by
    have h := Neutral.append (Expr.neutral l) (Neutral.append (neutral_binOp op) (Expr.neutral r))
    simpa [Expr.tokens, Expr.words] using h
  | .asConst _ l => by
    have h := Neutral.append (Expr.neutral l) (Neutral.all (ks := [.ident "as", .keyword "const"]) (by simp))
    rw [Expr.tokens_asConst]; exact h
  | .satisfies _ l t => by
    have h := Neutral.append (Expr.neutral l) (Neutral.cons (k := .ident "satisfies") (by simp) (TypeExpr.neutral t))
    rw [Expr.tokens_satisfies]; exact h
  | .spread _ v => by
    have h := Neutral.cons (k := .punct "...") (by simp) (Expr.neutral v)
    simpa [Expr.tokens, Expr.words, punctWord] using h
  | .cond _ t a b => by
    have h := Neutral.append (Expr.neutral t) (Neutral.cons (k := .punct "?") (by simp)
      (Neutral.append (Expr.neutral a) (Neutral.cons (k := .punct ":") (by simp) (Expr.neutral b))))
    simpa [Expr.tokens, Expr.words, punctWord] using h
  | .assign _ op t v => by
    have h := Neutral.append (Expr.neutral t) (Neutral.append (neutral_assignOp op) (Expr.neutral v))
    simpa [Expr.tokens, Expr.words] using h
  | .arrow _ parens ps b => by
    have hb := Neutral.cons (k := .punct "=>") (by simp) (Expr.neutral b)
    rw [Expr.tokens_arrow]
    rcases arrowParams_cases parens ps with ⟨p, _, _, hp⟩ | hp
    · rw [hp]; exact Neutral.append (Neutral.all (by simp [identWord])) hb
    · rw [hp, enclose_params_flatten]
      have h := Neutral.append (Neutral.enclosed (o := "(") (c := ")") (by simp) (by simp)
        (Neutral.join (xs := ps.map fun p => p.words.flatten)
          (fun x hx => by simp at hx; obtain ⟨p, _, rfl⟩ := hx; exact Param.neutral p))) hb
      simpa using h

theorem Expr.neutralAll : ∀ es : List Expr, ∀ x ∈ es.map Expr.tokens, Neutral x
  | [], _, h => by simp at h
  | e :: es, x, h => by
    simp at h
    rcases h with rfl | h
    · exact Expr.neutral e
    · exact Expr.neutralAll es x (by simpa using h)

theorem Property.neutral : ∀ q : Property, Neutral q.tokens
  | .shorthand _ n => Neutral.all (by simp [Property.tokens, Property.words, identWord])
  | .keyValue _ k v => by
    have h := Neutral.append (neutral_key k) (Neutral.cons (k := .punct ":") (by simp) (Expr.neutral v))
    simpa [Property.tokens, Property.words, punctWord] using h
  | .spread _ v => by
    have h := Neutral.cons (k := .punct "...") (by simp) (Expr.neutral v)
    simpa [Property.tokens, Property.words, punctWord] using h

theorem Property.neutralAll : ∀ ps : List Property, ∀ x ∈ ps.map Property.tokens, Neutral x
  | [], _, h => by simp at h
  | p :: ps, x, h => by
    simp at h
    rcases h with rfl | h
    · exact Property.neutral p
    · exact Property.neutralAll ps x (by simpa using h)

end


/-- Two lists of tokens after an expression that `afterOK` cannot tell apart:
they start with the same token, and the scan for a `>` finds the same at
depth 0. -/
def AfterEquiv (a b : List TokenKind) : Prop := a.head? = b.head? ∧ closesKinds 0 a = closesKinds 0 b

theorem AfterEquiv.prepend {x a b : List TokenKind} (hx : Neutral x) (hne : x ≠ []) (h : AfterEquiv a b) :
    AfterEquiv (x ++ a) (x ++ b) := by
  refine ⟨?_, by rw [hx, hx, h.2]⟩
  cases x with
  | nil => exact absurd rfl hne
  | cons k x => simp

theorem AfterEquiv.closer {c : String} (hc : c ∈ [")", "]", "}"]) (a b : List TokenKind) :
    AfterEquiv (.punct c :: a) (.punct c :: b) :=
  ⟨rfl, by simp at hc; rcases hc with rfl | rfl | rfl <;> simp [closesKinds]⟩

theorem neutral_args (args : List Expr) : Neutral (enclose "(" ")" (Expr.wordsOf args)).flatten := by
  have h := Neutral.enclosed (o := "(") (c := ")") (by simp) (by simp) (Neutral.join (Expr.neutralAll args))
  simpa [enclose, punctWord, separated_flatten, Expr.wordsOf_eq, List.map_map, Function.comp_def] using h

mutual

/-- `afterOK` depends on what follows only through what `AfterEquiv` compares. -/
theorem Expr.afterOK_congr : ∀ (e : Expr) {a b : List TokenKind}, AfterEquiv a b → e.afterOK a = e.afterOK b
  | .arrow _ _ _ body, a, b, h => by simp only [Expr.afterOK, Expr.afterOK_congr body h]
  | .binary _ op l r, a, b, h => by
    obtain ⟨k, ks, hk, _⟩ := binOp_head op
    simp only [Expr.afterOK]
    rw [Expr.neutral r 0 a, Expr.neutral r 0 b, h.2, Expr.afterOK_congr r h,
      Expr.afterOK_congr l (AfterEquiv.prepend (Neutral.append (neutral_binOp op) (Expr.neutral r))
        (by simp [hk]) h)]
  | .paren _ i, a, b, h => by
    simp only [Expr.afterOK, notFirst, h.1, Expr.afterOK_congr i (AfterEquiv.closer (c := ")") (by simp) a b)]
  | .member _ o n, a, b, h => by
    simp only [Expr.afterOK]
    exact Expr.afterOK_congr o (AfterEquiv.prepend (x := .punct "." :: propertyName n)
      (Neutral.cons (by simp) (neutral_propertyName n)) (by simp) h)
  | .optMember _ o n, a, b, h => by
    simp only [Expr.afterOK]
    exact Expr.afterOK_congr o (AfterEquiv.prepend (x := .punct "?." :: propertyName n)
      (Neutral.cons (by simp) (neutral_propertyName n)) (by simp) h)
  | .index _ o i, a, b, h => by
    simp only [Expr.afterOK]
    have hx := Neutral.enclosed (o := "[") (c := "]") (by simp) (by simp) (Expr.neutral i)
    have ho := Expr.afterOK_congr o (AfterEquiv.prepend hx (by simp) h)
    simp only [List.cons_append, List.append_assoc, List.nil_append] at ho ⊢
    rw [ho, Expr.afterOK_congr i (AfterEquiv.closer (c := "]") (by simp) a b)]
  | .call _ c as, a, b, h => by
    simp only [Expr.afterOK]
    rw [Expr.afterOK_congr c (AfterEquiv.prepend (neutral_args as) (by simp [enclose, punctWord]) h),
      Expr.afterOKList_congr as (AfterEquiv.closer (c := ")") (by simp) a b)]
  | .unary _ _ x, a, b, h | .prefix _ _ x, a, b, h => by
    simp only [Expr.afterOK]; exact Expr.afterOK_congr x h
  | .postfix _ op x, a, b, h => by
    simp only [Expr.afterOK]
    exact Expr.afterOK_congr x (AfterEquiv.prepend (x := [.punct op.symbol]) (neutral_updateOp op) (by simp) h)
  | .asConst _ x, a, b, h => by
    simp only [Expr.afterOK]
    have hc := Expr.afterOK_congr x (AfterEquiv.prepend (x := [.ident "as", .keyword "const"]) (Neutral.all (by simp))
      (by simp) h)
    simpa only [List.cons_append, List.nil_append] using hc
  | .satisfies _ x t, a, b, h => by
    simp only [Expr.afterOK]
    exact Expr.afterOK_congr x (AfterEquiv.prepend (Neutral.cons (by simp) (TypeExpr.neutral t)) (by simp) h)
  | .spread _ x, a, b, h => by simp only [Expr.afterOK]; exact Expr.afterOK_congr x h
  | .cond _ t x y, a, b, h => by
    simp only [Expr.afterOK]
    have hy := AfterEquiv.prepend (x := .punct ":" :: y.tokens) (Neutral.cons (by simp) (Expr.neutral y))
      (by simp) h
    have hx := AfterEquiv.prepend (x := .punct "?" :: x.tokens ++ .punct ":" :: y.tokens)
      (Neutral.cons (by simp) (Neutral.append (Expr.neutral x) (Neutral.cons (by simp) (Expr.neutral y))))
      (by simp) h
    rw [Expr.afterOK_congr t hx, Expr.afterOK_congr x hy, Expr.afterOK_congr y h]
  | .assign _ op t v, a, b, h => by
    obtain ⟨k, ks, hk, _⟩ := assignOp_head op
    simp only [Expr.afterOK]
    rw [Expr.afterOK_congr v h, Expr.afterOK_congr t (AfterEquiv.prepend
      (Neutral.append (neutral_assignOp op) (Expr.neutral v)) (by simp [hk]) h)]
  | .array _ es, a, b, h => by
    simp only [Expr.afterOK]
    exact Expr.afterOKList_congr es (AfterEquiv.closer (c := "]") (by simp) a b)
  | .object _ ps, a, b, h => by
    simp only [Expr.afterOK]
    exact Property.afterOKList_congr ps (AfterEquiv.closer (c := "}") (by simp) a b)
  | .new _ _ _ as, a, b, h => by
    simp only [Expr.afterOK]
    exact Expr.afterOKList_congr as (AfterEquiv.closer (c := ")") (by simp) a b)
  | .ident .., _, _, _ | .number .., _, _, _ | .bigint .., _, _, _ | .string .., _, _, _
  | .bool .., _, _, _ | .null _, _, _, _ => rfl

theorem Expr.afterOKList_congr : ∀ (es : List Expr) {c c' : List TokenKind}, AfterEquiv c c' →
    Expr.afterOKList c es = Expr.afterOKList c' es
  | [], _, _, _ => rfl
  | [e], _, _, h => by simp only [Expr.afterOKList]; exact Expr.afterOK_congr e h
  | e :: f :: es, _, _, h => by
    simp only [Expr.afterOKList]
    rw [Expr.afterOK_congr e (AfterEquiv.prepend (x := .punct "," :: joined "," ((f :: es).map Expr.tokens))
      (Neutral.cons (by simp) (Neutral.join (Expr.neutralAll (f :: es)))) (by simp) h),
      Expr.afterOKList_congr (f :: es) h]

theorem Property.afterOK_congr : ∀ (q : Property) {a b : List TokenKind}, AfterEquiv a b →
    q.afterOK a = q.afterOK b
  | .shorthand .., _, _, _ => rfl
  | .keyValue _ _ v, _, _, h | .spread _ v, _, _, h => by
    simp only [Property.afterOK]; exact Expr.afterOK_congr v h

theorem Property.afterOKList_congr : ∀ (ps : List Property) {c c' : List TokenKind}, AfterEquiv c c' →
    Property.afterOKList c ps = Property.afterOKList c' ps
  | [], _, _, _ => rfl
  | [q], _, _, h => by simp only [Property.afterOKList]; exact Property.afterOK_congr q h
  | q :: r :: ps, _, _, h => by
    simp only [Property.afterOKList]
    rw [Property.afterOK_congr q (AfterEquiv.prepend
      (x := .punct "," :: joined "," ((r :: ps).map Property.tokens))
      (Neutral.cons (by simp) (Neutral.join (Property.neutralAll (r :: ps)))) (by simp) h),
      Property.afterOKList_congr (r :: ps) h]

end

/-- What `afterOK` checks before a `;` does not depend on what follows the `;`. -/
theorem afterOK_semicolon {e : Expr} (h : e.afterOK [.punct ";"] = true) (x : List TokenKind) :
    e.afterOK (.punct ";" :: x) = true := by
  rw [Expr.afterOK_congr e (a := .punct ";" :: x) (b := [.punct ";"]) ⟨rfl, by simp [closesKinds]⟩]; exact h


/-! ### Fuel from the budget -/

theorem length_symbol_binOp (op : BinOp) : 1 ≤ (symbol op.symbol).length := by
  obtain ⟨k, ks, hk, _⟩ := binOp_head op; simp [hk]

theorem length_symbol_assignOp (op : AssignOp) : 1 ≤ (symbol op.symbol).length := by
  obtain ⟨k, ks, hk, _⟩ := assignOp_head op; simp [hk]

theorem length_symbol_unaryOp (op : UnaryOp) : 1 ≤ (symbol op.symbol).length := by
  obtain ⟨k, hk, _⟩ := unaryOp_symbol op; simp [hk]

mutual

/-- An expression nests no deeper than it has tokens. -/
theorem Expr.height_le : ∀ e : Expr, e.height ≤ e.tokens.length
  | .ident .. | .number .. | .bigint .. | .string .. | .bool .. | .null _ => by simp [Expr.height]
  | .array _ es => by
    have := Expr.heightOf_le es
    rw [Expr.tokens_array]; simp only [Expr.height, List.length_cons, List.length_append, List.length_nil]
    omega
  | .object _ ps => by
    have := Property.heightOf_le ps
    rw [Expr.tokens_object]; simp only [Expr.height, List.length_cons, List.length_append, List.length_nil]
    omega
  | .paren _ i => by
    have := Expr.height_le i
    rw [Expr.tokens_paren]; simp only [Expr.height, List.length_cons, List.length_append, List.length_nil]
    omega
  | .member _ o n => by
    have := Expr.height_le o
    rw [Expr.tokens_member]; simp only [Expr.height, List.length_cons, List.length_append, length_propertyName]
    omega
  | .optMember _ o n => by
    have := Expr.height_le o
    rw [Expr.tokens_optMember]; simp only [Expr.height, List.length_cons, List.length_append, length_propertyName]
    omega
  | .index _ o i => by
    have := Expr.height_le o; have := Expr.height_le i
    rw [Expr.tokens_index]; simp only [Expr.height, List.length_cons, List.length_append, List.length_nil]
    omega
  | .call _ c as => by
    have := Expr.height_le c; have := Expr.heightOf_le as
    rw [Expr.tokens_call]; simp only [Expr.height, List.length_cons, List.length_append, List.length_nil]
    omega
  | .new _ c ts as => by
    have := Expr.heightOf_le as
    rw [Expr.tokens_new]; simp only [Expr.height, List.length_cons, List.length_append, List.length_nil]
    omega
  | .asConst _ l => by
    have := Expr.height_le l
    rw [Expr.tokens_asConst]; simp only [Expr.height, List.length_cons, List.length_append, List.length_nil]
    omega
  | .satisfies _ l t => by
    have := Expr.height_le l
    rw [Expr.tokens_satisfies]; simp only [Expr.height, List.length_cons, List.length_append]
    omega
  | .spread _ v => by
    have := Expr.height_le v
    simp only [Expr.height, Expr.tokens, Expr.words, punctWord, List.flatten_cons, List.length_append,
      List.length_cons]
    simp only [Expr.tokens] at this; omega
  | .unary _ op a => by
    have := Expr.height_le a; have := length_symbol_unaryOp op
    rw [Expr.tokens_unary]; simp only [Expr.height, List.length_append]
    omega
  | .prefix _ op a => by
    have := Expr.height_le a
    rw [Expr.tokens_prefix]; simp only [Expr.height, List.length_cons]
    omega
  | .postfix _ op a => by
    have := Expr.height_le a
    rw [Expr.tokens_postfix]; simp only [Expr.height, List.length_append, List.length_cons, List.length_nil]
    omega
  | .binary _ op l r => by
    have := Expr.height_le l; have := Expr.height_le r; have := length_symbol_binOp op
    rw [Expr.tokens_binary]; simp only [Expr.height, List.length_append]
    omega
  | .cond _ t a b => by
    have := Expr.height_le t; have := Expr.height_le a; have := Expr.height_le b
    rw [Expr.tokens_cond]; simp only [Expr.height, List.length_append, List.length_cons]
    omega
  | .assign _ op t v => by
    have := Expr.height_le t; have := Expr.height_le v; have := length_symbol_assignOp op
    rw [Expr.tokens_assign]; simp only [Expr.height, List.length_append]
    omega
  | .arrow _ parens ps b => by
    have := Expr.height_le b
    rw [Expr.tokens_arrow]; simp only [Expr.height, List.length_cons, List.length_append]
    omega

theorem Expr.heightOf_le : ∀ es : List Expr, Expr.heightOf es ≤ (joined "," (es.map Expr.tokens)).length
  | [] => by simp [Expr.heightOf, joined]
  | [e] => by have := Expr.height_le e; simp [Expr.heightOf, joined]; omega
  | e :: f :: es => by
    have := Expr.height_le e; have := Expr.heightOf_le (f :: es)
    show max e.height (Expr.heightOf (f :: es)) ≤
      (e.tokens ++ .punct "," :: joined "," ((f :: es).map Expr.tokens)).length
    simp only [List.length_append, List.length_cons]; omega

theorem Property.height_le : ∀ q : Property, q.height ≤ q.tokens.length
  | .shorthand .. => by simp [Property.height]
  | .keyValue _ k v => by
    have := Expr.height_le v
    rw [Property.tokens_keyValue]; simp only [Property.height, List.length_append, List.length_cons]
    omega
  | .spread _ v => by
    have := Expr.height_le v
    simp only [Property.height, Property.tokens, Property.words, punctWord, List.flatten_cons,
      List.length_append, List.length_cons]
    simp only [Expr.tokens] at this; omega

theorem Property.heightOf_le : ∀ ps : List Property,
    Property.heightOf ps ≤ (joined "," (ps.map Property.tokens)).length
  | [] => by simp [Property.heightOf, joined]
  | [q] => by have := Property.height_le q; simp [Property.heightOf, joined]; omega
  | q :: r :: ps => by
    have := Property.height_le q; have := Property.heightOf_le (r :: ps)
    show max q.height (Property.heightOf (r :: ps)) ≤
      (q.tokens ++ .punct "," :: joined "," ((r :: ps).map Property.tokens)).length
    simp only [List.length_append, List.length_cons]; omega

end


/-- `need` fits in the fuel that `budget` gives for the tokens of `e` and what follows them. -/
theorem need_le_budget {e : Expr} {level : Level} {s : ParseState} {ts rest : List Token}
    (hs : s.rest = ts ++ rest) (hl : s.left = s.rest.length) (ht : Touching ts e.words) :
    need level e + 1 ≤ 10 * (s.left + 1) := by
  have h1 := Expr.height_le e
  have h2 : ts.length = e.tokens.length := by
    have := congrArg List.length ht.kinds; simpa [Expr.tokens] using this
  have h3 : ts.length ≤ s.left := by rw [hl, hs, List.length_append]; omega
  have h4 : level.cost ≤ 8 := by cases level <;> simp
  simp only [need]; omega

/-- `parseAssign`, with the fuel that `budget` gives, reads every assignment
expression. -/
theorem parseAssign_budget {T : Edition} (e : Expr) (he : e.wfAt T .assign = true) :
    ∀ (s : ParseState) (ts rest : List Token), s.target = T → s.rest = ts ++ rest →
      s.left = s.rest.length → Touching ts e.words → (∀ y ∈ ts.tail, NoBreak y) →
      rest ≠ [] → EndsAssign rest → e.afterOK (rest.map (·.kind)) = true →
      ∃ e' s', Parse.parseAssign (10 * (s.left + 1)) s = .ok e' s' ∧ e'.erase = e.erase ∧ Leaves s s' rest :=
  fun s ts rest hT hs hl ht hn hr hE ha =>
    exprs_read T (10 * (s.left + 1)) .assign e he (by have := need_le_budget (level := .assign) hs hl ht; omega)
      s ts rest hT hs hl ht hn hr hE ha

/-- `parseExpression`, with the fuel that `budget` gives, reads every
assignment expression that no `,` follows. -/
theorem parseExpression_budget {T : Edition} (e : Expr) (he : e.wfAt T .assign = true) :
    ∀ (s : ParseState) (ts rest : List Token), s.target = T → s.rest = ts ++ rest →
      s.left = s.rest.length → Touching ts e.words → (∀ y ∈ ts.tail, NoBreak y) →
      rest ≠ [] → EndsExpr rest → e.afterOK (rest.map (·.kind)) = true →
      ∃ e' s', Parse.parseExpression (10 * (s.left + 1)) s = .ok e' s' ∧ e'.erase = e.erase ∧
        Leaves s s' rest := by
  intro s ts rest hT hs hl ht hn hr hE ha
  have hb := need_le_budget (level := .assign) hs hl ht
  obtain ⟨g, hg⟩ : ∃ g, 10 * (s.left + 1) = g + 1 := ⟨10 * s.left + 9, by omega⟩
  rw [hg]
  exact expression_reads g e (exprs_read T g .assign e he (by omega)) s ts rest hT hs hl ht hn hr hE ha

end tolean.TypeScript.Syntax
