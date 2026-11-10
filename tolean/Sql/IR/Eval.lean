import tolean.Sql.IR

/-!
The meaning of the SQL IR: what the printed code computes, over the values
of the interpreter in `tolean/Sql/Spec/Eval.lean`.

Each operation is the interpreter's own. What differs is how the rows are
found. A lookup reads the rows of a table whose key equals the key that it
computes, as `Pg.lookup` reads a table's row by its key. It gives no value
when a key is NULL or of another kind, because the printed code never meets
such a key.
-/
namespace tolean.Sql.IR

open tolean tolean.Sql
open tolean.Sql.Eval (M Val Row Input stuck)

/-- The value of an expression. The innermost row comes first in `env`. -/
def Expr.eval (i : Input) (env : List Row) : Expr → M Val
  | .col d j _ _ =>
    match env[d]? with
    | some r => match r[j]? with
      | some v => pure v
      | none => stuck
    | none => stuck
  | .int n => Eval.intLit n
  | .bool b => pure (.bool b)
  | .text s => pure (.text s)
  | .enumLit t l => pure (.enum t l)
  | .arg n _ =>
    match i.args.lookup n with
    | some v => pure v
    | none => stuck
  | .now => pure (.ts i.now)
  | .arith op a b => Eval.arithM op (a.eval i env) (b.eval i env)
  | .neg a => Eval.negM (a.eval i env)
  | .eq ne a b => Eval.eqM ne (a.eval i env) (b.eval i env)
  | .cmp op a b => Eval.cmpM op (a.eval i env) (b.eval i env)
  | .and a b => Eval.andM (a.eval i env) (b.eval i env)
  | .or a b => Eval.orM (a.eval i env) (b.eval i env)
  | .not a => Eval.notM (a.eval i env)
  | .isNull negated _ a => Eval.isNullM negated (a.eval i env)
  | .cast t a => a.eval i env >>= Eval.castVal t
  | .enumText _ _ a => a.eval i env >>= Eval.castVal .text
  | .least a b => Eval.leastM (a.eval i env) (b.eval i env)
  | .coalesce _ a b => Eval.coalesceM (a.eval i env) (b.eval i env)

/-- The rows of `rows` whose column `j` equals `k`. -/
def lookupRows (j : Nat) (k : Val) : List Row → M (List Row)
  | [] => pure []
  | r :: rows => do
    let v ← match r[j]? with
      | some v => pure v
      | none => stuck
    let b ← Eval.eq3 v k
    let rest ← lookupRows j k rows
    match b with
    | some true => pure (r :: rest)
    | some false => pure rest
    | none => stuck

def Select.emit (i : Input) (s : Select) (env : List Row) : M (List Row) := do
  let c ← Eval.andAll (s.conds.map fun e => e.eval i env >>= Eval.truth)
  if c = some true then
    let row ← s.outs.mapM (·.eval i env)
    pure [row]
  else pure []

/-- The nested lookups. -/
def loop (i : Input) (body : List Row → M (List Row)) : List Lookup → List Row → M (List Row)
  | [], env => body env
  | l :: rest, env => do
    let k ← l.key.eval i env
    let rows ← lookupRows l.keyIndex k (i.db l.table)
    Eval.flatMapM rows fun r => loop i body rest (r :: env)

/-- The rows the query returns and the database after it. -/
def Query.run (qy : Query) (i : Input) : M (List Row × Eval.DB) := do
  let rows ← loop i (qy.select.emit i) qy.select.lookups []
  pure (← qy.kind.result rows, i.db)

end tolean.Sql.IR
