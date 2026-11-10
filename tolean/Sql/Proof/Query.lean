import tolean.Sql.Proof.Expr

/-!
The plan of a `SELECT` means what the `SELECT` means. `translate_sound`
states it for every query that `Plan.translate` accepts.

The interpreter scans every row of every table in `FROM`, but the plan reads
only the rows whose key column equals the key. `lookups_sound` proves that
both give the same output rows. The translator takes the key from a
condition `alias.key = e` of the query. On a row whose key column holds
another value, that condition is false. The key `e` reads no table that
comes after the alias, so `eval_weaken` shows that it has the same value
inside the scan. So the whole condition is false on that row, and the scan
gives no output row for it.

The conditions also differ in shape. The translator splits them at `AND`,
but the interpreter evaluates each `ON` and the `WHERE` as written.
`split_sound` shows that the split conditions give the same value, because
`and3` is associative wherever it gives a value.
-/
namespace tolean.Sql.Proof

open tolean tolean.Sql
open tolean.Sql.Eval
open tolean.Sql.Plan (TM St reject trExpr Scope Entry T)

/-! ### Conditions -/

abbrev Cond := M (Option Bool)

theorem and3_true_right (x : Cond) : and3 x (.ok (some true)) = x := by
  rcases x with e | (_ | _ | _) <;> rfl

theorem and3_true_left (x : Cond) : and3 (.ok (some true)) x = x := by
  rcases x with e | (_ | _ | _) <;> rfl

theorem and3_false_right (x : Cond) : and3 x (.ok (some false)) = .ok (some false) := by
  rcases x with e | (_ | _ | _) <;> rfl

theorem andAll_cons (x : Cond) (xs : List Cond) : andAll (x :: xs) = and3 x (andAll xs) := by
  cases xs with
  | nil => exact (and3_true_right x).symm
  | cons y ys => rfl

theorem and3_assoc (a b c : Cond) : Refines (and3 a (and3 b c)) (and3 (and3 a b) c) := by
  intro v h
  rcases a with _ | (_ | _ | _) <;> rcases b with _ | (_ | _ | _) <;> rcases c with _ | (_ | _ | _) <;>
    simp only [and3, reduceCtorEq, Except.ok.injEq] at h <;> subst h <;> rfl

/-- Two lists, related element by element. -/
inductive Pw {α β : Type} (R : α → β → Prop) : List α → List β → Prop
  | nil : Pw R [] []
  | cons {a b as bs} : R a b → Pw R as bs → Pw R (a :: as) (b :: bs)

theorem andAll_mono {xs ys : List Cond} (h : Pw Refines xs ys) : Refines (andAll xs) (andAll ys) := by
  induction h with
  | nil => exact .refl _
  | cons hxy _ ih => rw [andAll_cons, andAll_cons]; exact and3_mono hxy ih

theorem Refines.trans {x y z : M α} (h₁ : Refines x y) (h₂ : Refines y z) : Refines x z :=
  fun v h => h₂ v (h₁ v h)

theorem andAll_append (xs ys : List Cond) : Refines (andAll (xs ++ ys)) (and3 (andAll xs) (andAll ys)) := by
  induction xs with
  | nil =>
    show Refines (andAll ys) (and3 (.ok (some true)) (andAll ys))
    rw [and3_true_left]; exact .refl _
  | cons x xs ih =>
    rw [List.cons_append, andAll_cons, andAll_cons]
    exact (and3_mono (.refl x) ih).trans (and3_assoc _ _ _)

theorem andAll_false {xs : List Cond} (h : .ok (some false) ∈ xs) : andAll xs = .ok (some false) := by
  induction xs with
  | nil => cases h
  | cons x xs ih =>
    rw [andAll_cons]
    rcases List.mem_cons.mp h with rfl | h
    · rfl
    · rw [ih h, and3_false_right]

variable (s : Schema) (i : Input) (env : List Binding)

/-- A condition, as `WHERE` reads it. -/
def ev (e : Expr) : Cond := Eval.eval s i env e >>= truth

theorem truth_ofTruth (x : Option Bool) : truth (ofTruth x) = .ok x := by
  rcases x with _ | (_ | _) <;> rfl

theorem ev_and {sp : Span} {op : String} {a b : Expr} (hop : BinOp.ofString op = some .and) :
    ev s i env (.binary sp op a b) = and3 (ev s i env a) (ev s i env b) := by
  simp only [ev, Eval.eval, hop, Eval.binary]
  unfold Eval.andM
  generalize and3 _ _ = c
  rcases c with e | x
  · rfl
  · exact truth_ofTruth x

theorem conjuncts_sound : ∀ e : Expr, Refines (andAll ((Plan.conjuncts e).map (ev s i env))) (ev s i env e)
  | .binary sp op a b => by
    by_cases hop : BinOp.ofString op = some .and
    · simp only [Plan.conjuncts, hop, ↓reduceIte, List.map_append]
      rw [ev_and s i env hop]
      exact (andAll_append _ _).trans (and3_mono (conjuncts_sound a) (conjuncts_sound b))
    · simp only [Plan.conjuncts, hop, ↓reduceIte, List.map_cons, List.map_nil, andAll]
      exact .refl _
  | .column .. | .int .. | .str .. | .bool .. | .null .. | .arg .. | .cast .. | .typedLit .. | .unary ..
  | .isNull .. | .call .. | .exists .. | .subquery .. => by
    simp only [Plan.conjuncts, List.map_cons, List.map_nil, andAll]; exact .refl _

/-- The conditions split at `AND` mean what the conditions mean. -/
theorem split_sound (es : List Expr) :
    Refines (andAll ((es.flatMap Plan.conjuncts).map (ev s i env))) (andAll (es.map (ev s i env))) := by
  induction es with
  | nil => exact .refl _
  | cons e es ih =>
    rw [List.flatMap_cons, List.map_append, List.map_cons, andAll_cons]
    exact (andAll_append _ _).trans (and3_mono (conjuncts_sound s i env e) ih)


/-! ### Names that an expression does not read -/

theorem aliasIndex_append {new S : List Shape} {a : String} (h : ∀ x ∈ new, x.1 ≠ a) :
    aliasIndex (new ++ S) a = (aliasIndex S a).map (· + new.length) := by
  induction new with
  | nil => simp
  | cons x new ih =>
    obtain ⟨b, t⟩ := x
    have hb : b ≠ a := h (b, t) List.mem_cons_self
    simp only [List.cons_append, aliasIndex, hb, ↓reduceIte]
    rw [ih fun x hx => h x (List.mem_cons_of_mem _ hx)]
    cases aliasIndex S a <;> simp [Nat.add_assoc]

theorem resolve_append {new S : List Shape} {a n : String} (h : ∀ x ∈ new, x.1 ≠ a) :
    resolve (new ++ S) (some a) n = (resolve S (some a) n).map fun p => (p.1 + new.length, p.2) := by
  simp only [resolve, aliasIndex_append h]
  cases aliasIndex S a with
  | none => rfl
  | some k =>
    have hk : (new ++ S)[k + new.length]? = S[k]? := by
      rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel]
    simp only [Option.bind_eq_bind, Option.map_some, Option.bind_some, hk]
    cases S[k]? with
    | none => rfl
    | some p =>
      simp only [Option.bind_some]
      cases colIndex p.2 n <;> rfl

theorem column_append {new benv : List Binding} {k j : Nat} :
    column (new ++ benv) (k + new.length, j) = column benv (k, j) := by
  simp only [column]
  rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel]

section
variable (s : Schema) (i : Input)

mutual

/-- Bindings for aliases that `e` does not read do not change its value. -/
theorem eval_weaken (new benv : List Binding) :
    ∀ e : Expr, (∀ b ∈ new, Plan.reads b.alias e = false) →
      Eval.eval s i (new ++ benv) e = Eval.eval s i benv e
  | .column _ (some q) n, h => by
    have hq : ∀ x ∈ new.map Binding.shape, x.1 ≠ q := by
      intro x hx
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
      have := h b hb
      simp only [Plan.reads, beq_eq_false_iff_ne] at this
      exact fun e => this e.symm
    simp only [Eval.eval, List.map_append, resolve_append hq]
    cases resolve (benv.map Binding.shape) (some q) n with
    | none => rfl
    | some p =>
      simp only [Option.map_some]
      rw [List.length_map]
      exact column_append
  | .column _ none n, h => by
    cases new with
    | nil => rfl
    | cons b _ => exact absurd (h b List.mem_cons_self) (by simp [Plan.reads])
  | .int .., _ | .str .., _ | .bool .., _ | .null .., _ | .arg .., _ | .typedLit .., _
  | .exists .., _ | .subquery .., _ => by simp only [Eval.eval]
  | .cast _ x tn, h => by
    simp only [Eval.eval]
    rw [eval_weaken new benv x (by simpa [Plan.reads] using h)]
  | .unary _ op x, h => by
    simp only [Eval.eval]
    rw [eval_weaken new benv x (by simpa [Plan.reads] using h)]
  | .isNull _ x _, h => by
    simp only [Eval.eval]
    rw [eval_weaken new benv x (by simpa [Plan.reads] using h)]
  | .binary _ op x y, h => by
    simp only [Plan.reads, Bool.or_eq_false_iff] at h
    simp only [Eval.eval]
    rw [eval_weaken new benv x fun b hb => (h b hb).1, eval_weaken new benv y fun b hb => (h b hb).2]
  | .call _ f xs, h => by
    simp only [Eval.eval]
    exact evalCall_weaken new benv _ xs (by simpa [Plan.reads] using h)

theorem evalCall_weaken (new benv : List Binding) (f : Option Fn) :
    ∀ xs : List Expr, (∀ b ∈ new, Plan.readsList b.alias xs = false) →
      Eval.evalCall s i (new ++ benv) f xs = Eval.evalCall s i benv f xs
  | [], _ => by simp only [Eval.evalCall]
  | x :: xs, h => by
    simp only [Plan.readsList, Bool.or_eq_false_iff] at h
    simp only [Eval.evalCall]
    rw [eval_weaken new benv x fun b hb => (h b hb).1, evalCall_weaken new benv f xs fun b hb => (h b hb).2]

end

end

theorem eq3_comm (a b : Val) : eq3 a b = eq3 b a := by
  cases a <;> cases b <;> simp only [eq3] <;>
    first
    | rfl
    | (rename_i t l t' l'
       by_cases h : t = t'
       · subst h; simp [Bool.beq_comm]
       · rw [if_neg h, if_neg (Ne.symm h)])
    | (simp only [Bool.beq_comm]; done)
    | simp [beq_comm]


/-! ### Reading a table by its key -/

/-- The condition that gives a table its key. -/
def KeyConj (qual : Option String) (k : String) (key c : Expr) : Prop :=
  (∃ sp sp', c = .binary sp "=" (.column sp' qual k) key) ∨
  (∃ sp sp', c = .binary sp "=" key (.column sp' qual k))

theorem keyCand_spec {alias k : String} {unbound : List String} {c : Expr} {qual : Option String}
    {key : Expr} (h : Plan.keyCand alias k unbound c = some (qual, key)) :
    KeyConj qual k key c ∧ Plan.keyOK alias unbound key = true := by
  unfold Plan.keyCand at h
  split at h
  · rename_i sp op l r
    by_cases hop : op = "="
    · subst hop
      simp only [↓reduceIte] at h
      split at h
      · rename_i sp' qual' col
        split at h
        · rename_i hc
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          simp only [Bool.and_eq_true, beq_iff_eq] at hc
          obtain ⟨⟨_, rfl⟩, hk⟩ := hc
          exact ⟨.inl ⟨sp, sp', rfl⟩, hk⟩
        · cases h
      · split at h
        · rename_i sp' qual' col
          split at h
          · rename_i hc
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            simp only [Bool.and_eq_true, beq_iff_eq] at hc
            obtain ⟨⟨_, rfl⟩, hk⟩ := hc
            exact ⟨.inr ⟨sp, sp', rfl⟩, hk⟩
          · cases h
        · cases h
    · simp only [hop, ↓reduceIte] at h; cases h
  · cases h

theorem keyFor_spec {alias k : String} {unbound : List String} {qual : Option String} {key : Expr} :
    ∀ {conds : List Expr}, Plan.keyFor alias k unbound conds = some (qual, key) →
      (∃ c ∈ conds, KeyConj qual k key c) ∧ Plan.keyOK alias unbound key = true
  | [], h => by cases h
  | c :: cs, h => by
    simp only [Plan.keyFor] at h
    split at h
    · rename_i r hr
      cases h
      obtain ⟨hc, hk⟩ := keyCand_spec hr
      exact ⟨⟨c, List.mem_cons_self, hc⟩, hk⟩
    · obtain ⟨⟨c', hc', hk'⟩, hok⟩ := keyFor_spec h
      exact ⟨⟨c', List.mem_cons_of_mem _ hc', hk'⟩, hok⟩

theorem ofString_eq : BinOp.ofString "=" = some .eq := rfl

/-- When the key column holds a value that is not the key, the condition is
false. -/
theorem keyConj_false {benv : List Binding} {qual : Option String} {k : String} {key c : Expr}
    {v kv : Val} (hc : KeyConj qual k key c) (hsp : ∀ sp, Eval.eval s i benv (.column sp qual k) = .ok v)
    (hkey : Eval.eval s i benv key = .ok kv) (hf : eq3 v kv = .ok (some false)) :
    Eval.eval s i benv c = .ok (.bool false) := by
  rcases hc with ⟨sp, sp', rfl⟩ | ⟨sp, sp', rfl⟩
  · show binary (BinOp.ofString "=") (Eval.eval s i benv (.column sp' qual k)) (Eval.eval s i benv key) = _
    rw [hsp, hkey, ofString_eq]
    simp [Eval.binary, eqM, bind, Except.bind, hf, pure, Except.pure, ofTruth]
  · show binary (BinOp.ofString "=") (Eval.eval s i benv key) (Eval.eval s i benv (.column sp' qual k)) = _
    rw [hsp, hkey, ofString_eq]
    simp [Eval.binary, eqM, bind, Except.bind, eq3_comm kv v, hf, pure, Except.pure, ofTruth]

theorem flatMapM_nil {α β : Type} {xs : List α} {f : α → M (List β)} (h : ∀ x ∈ xs, f x = .ok []) :
    flatMapM xs f = .ok [] := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [flatMapM, h x List.mem_cons_self, ih fun y hy => h y (List.mem_cons_of_mem _ hy)]
    rfl

/-- A scan whose every row fails the condition gives no row. -/
theorem scan_nil (body' : List Binding → M (List Row)) : ∀ (rest : List Shape) (benv : List Binding),
    (∀ ext : List Binding, ext.map Binding.shape = rest.reverse → body' (ext ++ benv) = .ok []) →
    Eval.scan i body' rest benv = .ok []
  | [], benv, h => by simpa [Eval.scan] using h [] rfl
  | (a, t) :: rest, benv, h => by
    simp only [Eval.scan]
    apply flatMapM_nil
    intro r _
    apply scan_nil body' rest
    intro ext hext
    have := h (ext ++ [⟨a, t, r⟩]) (by simp [hext, Binding.shape])
    simpa using this

theorem lookupRows_cons {j : Nat} {kv : Val} {r : Row} {R : List Row} {rows : List Row}
    (h : IR.lookupRows j kv (r :: R) = .ok rows) :
    ∃ v b rows', r[j]? = some v ∧ eq3 v kv = .ok (some b) ∧ IR.lookupRows j kv R = .ok rows' ∧
      rows = if b then r :: rows' else rows' := by
  simp only [IR.lookupRows] at h
  cases hv : r[j]? with
  | none => simp [hv, bind, Except.bind, stuck] at h
  | some v =>
    simp only [hv, bind, Except.bind, pure, Except.pure] at h
    cases he : eq3 v kv with
    | error e => simp [he] at h
    | ok b =>
      simp only [he] at h
      cases hr : IR.lookupRows j kv R with
      | error e => simp [hr] at h
      | ok rest =>
        simp only [hr] at h
        rcases b with _ | (_ | _)
        · simp [stuck] at h
        · simp only [Except.ok.injEq] at h
          exact ⟨v, false, rest, rfl, he, rfl, by simp [h]⟩
        · simp only [Except.ok.injEq] at h
          exact ⟨v, true, rest, rfl, he, rfl, by simp [h]⟩

theorem flatMapM_cons {α β : Type} {x : α} {xs : List α} {f : α → M (List β)} {out : List β}
    (h : flatMapM (x :: xs) f = .ok out) :
    ∃ ys zs, f x = .ok ys ∧ flatMapM xs f = .ok zs ∧ out = ys ++ zs := by
  simp only [flatMapM, bind, Except.bind] at h
  cases hx : f x with
  | error e => simp [hx] at h
  | ok ys =>
    cases hxs : flatMapM xs f with
    | error e => simp [hx, hxs] at h
    | ok zs => simp only [hx, hxs, pure, Except.pure, Except.ok.injEq] at h; exact ⟨ys, zs, rfl, rfl, h.symm⟩

theorem flatMapM_cons' {α β : Type} {x : α} {xs : List α} {f : α → M (List β)} {ys zs : List β}
    (hx : f x = .ok ys) (hxs : flatMapM xs f = .ok zs) : flatMapM (x :: xs) f = .ok (ys ++ zs) := by
  simp only [flatMapM, bind, Except.bind, hx, hxs]; rfl

/-- The rows that a lookup finds give what all the rows of the table give,
when a row that it skips gives none. -/
theorem rows_sound {j : Nat} {kv : Val} {f g : Row → M (List Row)} (hmatch : ∀ r, Refines (f r) (g r))
    (hskip : ∀ r v, r[j]? = some v → eq3 v kv = .ok (some false) → g r = .ok []) :
    ∀ (R rows : List Row) (out : List Row), IR.lookupRows j kv R = .ok rows →
      flatMapM rows f = .ok out → flatMapM R g = .ok out
  | [], rows, out, h, hout => by
    simp only [IR.lookupRows, pure, Except.pure, Except.ok.injEq] at h
    subst h
    simpa [flatMapM] using hout
  | r :: R, rows, out, h, hout => by
    obtain ⟨v, b, rows', hv, he, hR, rfl⟩ := lookupRows_cons h
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte] at hout
      have := flatMapM_cons' (hskip r v hv he) (rows_sound hmatch hskip R rows' out hR hout)
      simpa using this
    · simp only [↓reduceIte] at hout
      obtain ⟨ys, zs, hy, hz, rfl⟩ := flatMapM_cons hout
      exact flatMapM_cons' (hmatch r ys hy) (rows_sound hmatch hskip R rows' zs hR hz)

/-- The nested lookups give the rows that the nested scans give. A row that
a lookup skips has a key column that differs from the key, so the key's
condition is false on it, and the scans give no row for it. -/
theorem lookups_sound (conds : List Expr) (Γ : Scope)
    (body : List Row → M (List Row)) (body' : List Binding → M (List Row))
    (hB1 : ∀ benv : List Binding, benv.map Binding.shape = Γ.map Entry.shape →
      Refines (body (benv.map Binding.row)) (body' benv))
    (hB2 : ∀ benv : List Binding, benv.map Binding.shape = Γ.map Entry.shape →
      (∃ c ∈ conds, Eval.eval s i benv c = .ok (.bool false)) → body' benv = .ok []) :
    ∀ (rest : List Entry) (before : Scope) (st st' : St) (ls : List IR.Lookup),
    Plan.trLookups s conds (Γ.map Entry.shape) before rest st = .ok (ls, st') →
    Γ = rest.reverse ++ before →
    ∀ benv : List Binding, benv.map Binding.shape = before.map Entry.shape →
    Refines (IR.loop i body ls (benv.map Binding.row)) (Eval.scan i body' (rest.map Entry.shape) benv)
  | [], before, st, st', ls, h, hΓ, benv, hb => by
    simp only [Plan.trLookups, tm_pure_ok, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [List.reverse_nil, List.nil_append] at hΓ
    subst hΓ
    simp only [IR.loop, List.map_nil, Eval.scan]
    exact hB1 benv hb
  | e :: rest, before, st, st', ls, h, hΓ, benv, hb => by
    simp only [Plan.trLookups] at h
    tm_simp at h
    obtain ⟨k, _, ⟨_, rfl⟩, ⟨qual, key⟩, _, ⟨hkey, rfl⟩, j, _, ⟨_, rfl⟩, _, _, ⟨hres, rfl⟩,
      c, _, ⟨_, rfl⟩, kt, _, ⟨_, rfl⟩, ⟨ik, tk⟩, _, hik, _, _, ⟨hchk, rfl⟩, ls', _, hls, ⟨rfl, rfl⟩⟩ := h
    simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_true_eq] at hchk hres
    obtain ⟨⟨hnl, _⟩, _⟩ := hchk
    obtain ⟨⟨c₀, hc₀, hconj⟩, hok⟩ := keyFor_spec hkey
    have hΓ' : Γ = rest.reverse ++ e :: before := by simp [hΓ]
    -- The key, as the interpreter reads it.
    have hk := (expr_sound (s := s) (i := i) hb key _ _ _ _ _ hik).refines' hnl
    have ih := lookups_sound conds Γ body body' hB1 hB2 rest (e :: before) _ _ ls' hls hΓ'
    intro out hout
    simp only [IR.loop, bind, Except.bind] at hout
    cases hkv : ik.eval i (benv.map Binding.row) with
    | error _ => simp [hkv] at hout
    | ok kv =>
      simp only [hkv] at hout
      have hkeyv := hk kv hkv
      cases hrows : IR.lookupRows j kv (i.db e.table.name) with
      | error _ => simp [hrows] at hout
      | ok rows =>
        simp only [hrows] at hout
        simp only [List.map_cons, Entry.shape, Eval.scan]
        -- A row that the lookup skips gives no row.
        have hskip : ∀ r v, r[j]? = some v → eq3 v kv = .ok (some false) →
            Eval.scan i body' (rest.map Entry.shape) ({ alias := e.alias, table := e.table, row := r } :: benv) =
              .ok [] := by
          intro r v hv hf
          apply scan_nil i body'
          intro ext hext
          have hlen : ext.length = rest.length := by simpa using congrArg List.length hext
          have hshape : (ext ++ { alias := e.alias, table := e.table, row := r } :: benv).map Binding.shape =
              Γ.map Entry.shape := by
            rw [hΓ', List.map_append, hext, List.map_append, List.map_reverse]
            simp [Binding.shape, Entry.shape, hb]
          apply hB2 _ hshape
          refine ⟨c₀, hc₀, keyConj_false s i hconj (v := v) (kv := kv) ?_ ?_ hf⟩
          · intro sp
            simp only [Eval.eval, hshape, hres, column]
            rw [List.getElem?_append_right (by omega), hlen, Nat.sub_self]
            simp [hv]; rfl
          · rw [show ext ++ { alias := e.alias, table := e.table, row := r } :: benv =
                (ext ++ [{ alias := e.alias, table := e.table, row := r }]) ++ benv by simp]
            rw [eval_weaken s i]
            · exact hkeyv
            · intro b hb'
              simp only [Plan.keyOK, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
                List.any_eq_false] at hok
              rcases List.mem_append.mp hb' with hb' | hb'
              · have : b.alias ∈ rest.map (·.alias) := by
                  have := congrArg (List.map Prod.fst) hext
                  simp only [List.map_map, List.map_reverse] at this
                  have hm : b.alias ∈ ext.map (Prod.fst ∘ Binding.shape) := List.mem_map_of_mem hb'
                  rw [this] at hm
                  simpa [Entry.shape] using hm
                simpa using hok.1 _ this
              · simp only [List.mem_singleton] at hb'
                subst hb'
                simpa using hok.2
        -- Each row of the table, in order.
        exact rows_sound (fun r => ih ({ alias := e.alias, table := e.table, row := r } :: benv)
            (by simp [Binding.shape, Entry.shape, hb])) hskip _ rows out hrows hout


/-! ### `SELECT` -/

theorem entries_shapes : ∀ (from_ : List FromItem) (n : Nat) (st st' : St) (es : List Entry),
    Plan.entries s from_ n st = .ok (es, st') → fromShapes s from_ = .ok (es.map Entry.shape)
  | [], n, st, st', es, h => by
    simp only [Plan.entries, tm_pure_ok, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  | .mk table a on :: rest, n, st, st', es, h => by
    simp only [Plan.entries] at h
    tm_simp at h
    obtain ⟨t, _, ⟨ht, rfl⟩, es', _, hes, ⟨rfl, rfl⟩⟩ := h
    simp only [fromShapes, ht, entries_shapes rest (n + 1) _ _ es' hes, bind, Except.bind, pure,
      Except.pure, List.map_cons, Entry.shape]

theorem trConds_sound {Γ : Scope} {benv : List Binding} (hb : benv.map Binding.shape = Γ.map Entry.shape) :
    ∀ (conds : List Expr) (st st' : St) (ics : List IR.Expr), Plan.trConds s Γ conds st = .ok (ics, st') →
      Pw Refines (ics.map fun e => e.eval i (benv.map Binding.row) >>= truth) (conds.map (ev s i benv))
  | [], st, st', ics, h => by
    simp only [Plan.trConds, tm_pure_ok, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact .nil
  | c :: cs, st, st', ics, h => by
    simp only [Plan.trConds] at h
    tm_simp at h
    obtain ⟨⟨ic, t⟩, _, hc, _, _, ⟨ht, rfl⟩, rest, _, hrest, ⟨rfl, rfl⟩⟩ := h
    simp only [decide_eq_true_eq] at ht
    have := (expr_sound (s := s) (i := i) hb c _ _ _ _ _ hc).refines (by intro n; rw [ht]; simp)
    exact .cons (this.bind fun _ => .refl _) (trConds_sound hb cs _ _ rest hrest)

/-- An output column never is an enum label: it has no type to give one. -/
theorem out_refines {Γ : Scope} {benv : List Binding} (hb : benv.map Binding.shape = Γ.map Entry.shape)
    {e : Expr} {st st' : St} {ie : IR.Expr} {t : T} (h : trExpr s Γ none e st = .ok ((ie, t), st')) :
    Refines (ie.eval i (benv.map Binding.row)) (Eval.eval s i benv e) := by
  rcases expr_sound (s := s) (i := i) hb e _ _ _ _ _ h with ⟨sp, T, l, rfl, rfl, _⟩ | ⟨_, h'⟩
  · simp only [trExpr, Plan.strLit, tm_pure_ok, Prod.mk.injEq] at h
    cases h.1.1
  · exact h'

theorem mapM_cons_bind {α β : Type} (f : α → M β) (x : α) (xs : List α) :
    (x :: xs).mapM f = (do let y ← f x; let ys ← xs.mapM f; pure (y :: ys)) := by
  simp [List.mapM_cons]

theorem trOuts_sound {Γ : Scope} {benv : List Binding} (hb : benv.map Binding.shape = Γ.map Entry.shape) :
    ∀ (es : List Expr) (st st' : St) (outs : List (IR.Expr × T)), Plan.trOuts s Γ es st = .ok (outs, st') →
      Refines ((outs.map (·.1)).mapM fun e => e.eval i (benv.map Binding.row)) (es.mapM (Eval.eval s i benv))
  | [], st, st', outs, h => by
    simp only [Plan.trOuts, tm_pure_ok, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact .refl _
  | e :: es, st, st', outs, h => by
    simp only [Plan.trOuts] at h
    tm_simp at h
    obtain ⟨⟨ie, t⟩, _, he, rest, _, hrest, ⟨rfl, rfl⟩⟩ := h
    simp only [List.map_cons, mapM_cons_bind]
    exact (out_refines s i hb he).bind fun _ =>
      (trOuts_sound hb es _ _ rest hrest).bind fun _ => .refl _

theorem condsOf_eq (from_ : List FromItem) (where_ : Option Expr) :
    Plan.condsOf from_ where_ = (from_.filterMap onOf ++ where_.toList).flatMap Plan.conjuncts := by
  cases where_ <;> simp [Plan.condsOf]

theorem ev_false {benv : List Binding} {c : Expr} (h : Eval.eval s i benv c = .ok (.bool false)) :
    ev s i benv c = .ok (some false) := by
  simp [ev, h, bind, Except.bind, truth]; rfl

theorem select_sound {sel : Select} {st st' : St} {isel : IR.Select} {cols : List (String × IR.TyN)}
    (h : Plan.trSelect s sel st = .ok ((isel, cols), st')) :
    Refines (IR.loop i (isel.emit i) isel.lookups []) (Eval.select s i sel) := by
  obtain ⟨sp, items, from_, where_, fu⟩ := sel
  simp only [Plan.trSelect] at h
  tm_simp at h
  obtain ⟨es, _, hes, _, _, ⟨hd, rfl⟩, ls, _, hls, ics, _, hics, outs, _, houts, ⟨rfl, rfl⟩, rfl⟩ := h
  have hshapes := entries_shapes s from_ 1 _ _ es hes
  -- The body: the conditions and the output row.
  let trees := from_.filterMap onOf ++ where_.toList
  have hB1 : ∀ benv : List Binding, benv.map Binding.shape = es.reverse.map Entry.shape →
      Refines (IR.Select.emit i { lookups := ls, conds := ics, outs := outs.map (·.1) } (benv.map Binding.row))
        (Eval.emit s i trees (items.map itemExpr) benv) := by
    intro benv hb
    have hc := (andAll_mono (trConds_sound s i hb _ _ _ ics hics)).trans
      (by rw [condsOf_eq]; exact split_sound s i benv trees)
    exact hc.bind fun c => by
      by_cases hct : c = some true
      · simp only [hct, ↓reduceIte]
        exact (trOuts_sound s i hb _ _ _ outs houts).bind fun _ => .refl _
      · simp only [hct, ↓reduceIte]; exact .refl _
  have hB2 : ∀ benv : List Binding, benv.map Binding.shape = es.reverse.map Entry.shape →
      (∃ c ∈ Plan.condsOf from_ where_, Eval.eval s i benv c = .ok (.bool false)) →
      Eval.emit s i trees (items.map itemExpr) benv = .ok [] := by
    intro benv _ ⟨c, hc, hf⟩
    have hall : andAll (((trees.flatMap Plan.conjuncts)).map (ev s i benv)) = .ok (some false) := by
      rw [← condsOf_eq]
      exact andAll_false (List.mem_map.mpr ⟨c, hc, ev_false s i hf⟩)
    have := split_sound s i benv trees _ hall
    simp only [Eval.emit]
    show (andAll (trees.map (ev s i benv)) >>= _) = _
    rw [this]
    rfl
  have hl := lookups_sound s i (Plan.condsOf from_ where_) es.reverse _ _ hB1 hB2 es [] _ _ ls hls
    (by simp) [] rfl
  intro out hout
  have hscan := hl out hout
  simp only [Eval.select, hshapes, bind, Except.bind]
  have hd' : distinct ((es.map Entry.shape).map (·.1)) = true := by
    simpa [List.map_map, Function.comp_def, Entry.shape] using hd
  simp only [hd', Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  exact hscan

/-! ### Queries -/

/-- The plans that `Plan.translate` writes mean what their queries mean: when
the plan of a query gives a result for a database, the interpreter, which
scans every table, gives the same result for the source of the query. -/
theorem translate_sound {nq : NamedQuery} {qy : Query} {iq : IR.Query}
    (h : Plan.translate s nq qy = .ok iq) {out : List Row × DB} (hv : iq.run i = .ok out) :
    Eval.run s i nq.kind qy = .ok out := by
  simp only [Plan.translate] at h
  cases hk : Kind.ofString nq.kind with
  | none => simp [hk] at h
  | some kind =>
    simp only [hk] at h
    obtain ⟨ctes, main⟩ := qy
    cases ctes with
    | cons _ _ => simp at h
    | nil =>
      cases main with
      | update _ => simp at h
      | select sel =>
        simp only at h
        cases hsel : (Plan.trSelect s sel).run {} with
        | error _ => simp [hsel, bind, Except.bind] at h
        | ok r =>
          obtain ⟨⟨isel, cols⟩, st⟩ := r
          simp only [hsel, bind, Except.bind] at h
          split at h
          · cases h
          · simp only [pure, Except.pure, Except.ok.injEq] at h
            subst h
            have hs := select_sound s i (st := {}) hsel
            simp only [Eval.run, hk]
            simp only [IR.Query.run, bind, Except.bind] at hv
            cases hl : IR.loop i (isel.emit i) isel.lookups [] with
            | error _ => simp [hl] at hv
            | ok rows =>
              simp only [hl] at hv
              rw [hs rows hl]
              exact hv


end tolean.Sql.Proof
