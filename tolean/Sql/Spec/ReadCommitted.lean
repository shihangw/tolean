/-!
A model of PostgreSQL's READ COMMITTED isolation for single-row updates by
primary key, and two theorems about every interleaving of transactions.

The model follows the PostgreSQL documentation (§13.2.1, "Read Committed
Isolation Level"). Review it with care: the theorems are only as good as this
description of the server.

- An `UPDATE` of the row with key `k` works on the latest version of the row:
  the transaction's own version if it holds the row's lock, and otherwise the
  latest committed version. It can only run when no other transaction holds
  the lock; in PostgreSQL it waits until that transaction commits or aborts,
  and then re-checks its `WHERE` on the new version. So the update function
  sees the version that was current when the lock was granted.
- The update function returns the new row, or `none` when the `WHERE` does not
  hold. A row it changes stays locked until the transaction ends.
- `commit` writes the transaction's versions and releases its locks; `abort`
  drops them.
- Reads without a lock are not steps: they change nothing, and the theorems
  hold whatever a transaction does with what it read.

Two ghost fields record how much each transaction added to a numeric measure
`m` of each row. They change nothing else and exist only to state the second
theorem.
-/
namespace tolean.Pg.ReadCommitted

/-- A transaction. -/
abbrev Tid := Nat

structure World (Key Row : Type) where
  committed : Key → Option Row
  /-- The transaction that holds each row's lock. -/
  lock : Key → Option Tid
  /-- Each transaction's uncommitted version of the rows it locked. -/
  pending : Tid → Key → Option Row
  /-- The transaction has committed or aborted. -/
  done : Tid → Bool
  /-- Ghost: how much each transaction added to `m` of each row. -/
  added : Tid → Key → Int
  /-- Ghost: the transactions that committed, in order. -/
  committedTids : List Tid

def World.init {Key Row : Type} (rows : Key → Option Row) : World Key Row :=
  { committed := rows, lock := fun _ => none, pending := fun _ _ => none, done := fun _ => false,
    added := fun _ _ => 0, committedTids := [] }

inductive Step (Key Row : Type) where
  /-- `UPDATE … WHERE key = k`: `f` gives the new row, or `none` when the
  `WHERE` does not hold. -/
  | update (t : Tid) (k : Key) (f : Row → Option Row)
  | commit (t : Tid)
  | abort (t : Tid)

variable {Key Row : Type} [DecidableEq Key]

def upd {A B : Type} [DecidableEq A] (f : A → B) (a : A) (b : B) : A → B :=
  fun x => if x = a then b else f x

@[simp] theorem upd_same {A B : Type} [DecidableEq A] (f : A → B) (a : A) (b : B) :
    upd f a b a = b := by simp [upd]

@[simp] theorem upd_other {A B : Type} [DecidableEq A] (f : A → B) {a x : A} (b : B) (h : x ≠ a) :
    upd f a b x = f x := by simp [upd, h]

/-- The version of row `k` that an update by `t` works on. -/
def World.latest (w : World Key Row) (t : Tid) (k : Key) : Option Row :=
  if w.lock k = some t then w.pending t k else w.committed k

/-- A step can run now. -/
def World.enabled (w : World Key Row) : Step Key Row → Prop
  | .update t k _ => w.done t = false ∧ (w.lock k = none ∨ w.lock k = some t)
  | .commit t | .abort t => w.done t = false

instance (w : World Key Row) (s : Step Key Row) : Decidable (w.enabled s) := by
  cases s <;> simp only [World.enabled] <;> infer_instance

def World.step (m : Row → Int) (w : World Key Row) : Step Key Row → World Key Row
  | .update t k f =>
    match w.latest t k with
    | none => w
    | some r =>
      match f r with
      | none => w
      | some r' =>
        { w with lock := upd w.lock k (some t),
                 pending := upd w.pending t (upd (w.pending t) k (some r')),
                 added := upd w.added t (upd (w.added t) k (w.added t k + (m r' - m r))) }
  | .commit t =>
    { w with committed := fun k => if w.lock k = some t then w.pending t k else w.committed k,
             lock := fun k => if w.lock k = some t then none else w.lock k,
             done := upd w.done t true,
             committedTids := w.committedTids ++ [t] }
  | .abort t =>
    { w with lock := fun k => if w.lock k = some t then none else w.lock k,
             done := upd w.done t true }

/-- `steps` can run one after another from `w`. -/
def Runs (m : Row → Int) : World Key Row → List (Step Key Row) → Prop
  | _, [] => True
  | w, s :: ss => w.enabled s ∧ Runs m (w.step m s) ss

def run (m : Row → Int) : World Key Row → List (Step Key Row) → World Key Row
  | w, [] => w
  | w, s :: ss => run m (w.step m s) ss

/-- The updates in `steps` all keep `P`. -/
def AllKeep (P : Row → Prop) (steps : List (Step Key Row)) : Prop :=
  ∀ t k f, Step.update t k f ∈ steps → ∀ r r', P r → f r = some r' → P r'

/-! ## Theorem 1: a property every update keeps holds of every committed row -/

def Good (P : Row → Prop) (w : World Key Row) : Prop :=
  (∀ k r, w.committed k = some r → P r) ∧
  (∀ t k r, w.lock k = some t → w.pending t k = some r → P r)

omit [DecidableEq Key] in
theorem latest_good {P : Row → Prop} {w : World Key Row} (hg : Good P w) {t k r}
    (h : w.latest t k = some r) : P r := by
  unfold World.latest at h
  split at h
  · exact hg.2 t k r (by assumption) h
  · exact hg.1 k r h

theorem good_step {P : Row → Prop} {w : World Key Row} (m : Row → Int) (s : Step Key Row)
    (hkeep : ∀ t k f, s = .update t k f → ∀ r r', P r → f r = some r' → P r')
    (hg : Good P w) : Good P (w.step m s) := by
  cases s with
  | update t k f =>
    simp only [World.step]
    split
    · exact hg
    · rename_i r hr
      split
      · exact hg
      · rename_i r' hf
        have hr' := hkeep t k f rfl r r' (latest_good hg hr) hf
        refine ⟨hg.1, ?_⟩
        intro t' k' r'' hl hp
        by_cases hk : k' = k
        · subst hk
          simp at hl
          subst hl
          simp at hp
          subst hp
          exact hr'
        · simp only [upd_other _ _ hk] at hl
          by_cases ht : t' = t
          · subst ht
            simp [upd_other _ _ hk] at hp
            exact hg.2 _ _ _ hl hp
          · simp [upd_other _ _ ht] at hp
            exact hg.2 _ _ _ hl hp
  | commit t =>
    refine ⟨?_, ?_⟩
    · intro k r h
      simp only [World.step] at h
      split at h
      · exact hg.2 t k r (by assumption) h
      · exact hg.1 k r h
    · intro t' k r hl hp
      simp only [World.step] at hl hp
      split at hl
      · cases hl
      · exact hg.2 t' k r hl hp
  | abort t =>
    refine ⟨hg.1, ?_⟩
    intro t' k r hl hp
    simp only [World.step] at hl hp
    split at hl
    · cases hl
    · exact hg.2 t' k r hl hp

/-- **No committed row breaks `P`.** In every interleaving of transactions
whose updates all keep `P`, starting from rows that satisfy `P`, every
committed row, at every point, satisfies `P`. -/
theorem good_run (P : Row → Prop) (m : Row → Int) :
    ∀ (steps : List (Step Key Row)) (w : World Key Row), AllKeep P steps → Good P w →
      Good P (run m w steps) := by
  intro steps
  induction steps with
  | nil => intro w _ hg; exact hg
  | cons s ss ih =>
    intro w hk hg
    refine ih _ (fun t k f hmem => hk t k f (List.mem_cons_of_mem _ hmem)) ?_
    exact good_step m s (fun t k f hs => by subst hs; exact hk t k f (List.mem_cons_self ..)) hg

/-! ## Theorem 2: no lost updates -/

/-- What committed transactions added to row `k`. -/
def World.committedAdded (w : World Key Row) (k : Key) : Int :=
  (w.committedTids.map fun t => w.added t k).sum

/-- The invariant behind theorem 2. -/
def Acct (m : Row → Int) (init : Key → Option Row) (w : World Key Row) : Prop :=
  (∀ k r, w.committed k = some r → ∃ r0, init k = some r0 ∧ m r = m r0 + w.committedAdded k) ∧
  (∀ t k r, w.lock k = some t → w.pending t k = some r →
    ∃ rc, w.committed k = some rc ∧ m r = m rc + w.added t k) ∧
  (∀ t k, w.lock k = some t → (w.pending t k).isSome ∧ w.done t = false) ∧
  (∀ t k, w.done t = false → w.lock k ≠ some t → w.added t k = 0) ∧
  (∀ t, t ∈ w.committedTids → w.done t = true)

omit [DecidableEq Key] in
theorem acct_init (m : Row → Int) (rows : Key → Option Row) : Acct m rows (World.init rows) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro k r h; exact ⟨r, h, by simp [World.committedAdded, World.init]⟩
  · intro t k r h; simp [World.init] at h
  · intro t k h; simp [World.init] at h
  · intro t k _ _; rfl
  · intro t h; simp [World.init] at h

omit [DecidableEq Key] in
theorem committedAdded_frozen {w : World Key Row} {added' : Tid → Key → Int} (t : Tid)
    (hnot : t ∉ w.committedTids) (hsame : ∀ u, u ≠ t → added' u = w.added u) (k : Key) :
    (w.committedTids.map fun u => added' u k).sum = w.committedAdded k := by
  unfold World.committedAdded
  congr 1
  apply List.map_congr_left
  intro u hu
  have : u ≠ t := fun h => hnot (h ▸ hu)
  rw [hsame u this]

theorem acct_step {m : Row → Int} {init : Key → Option Row} {w : World Key Row} {s : Step Key Row}
    (he : w.enabled s) (ha : Acct m init w) : Acct m init (w.step m s) := by
  obtain ⟨hc, hp, hl, hz, hd⟩ := ha
  cases s with
  | update t k f =>
    obtain ⟨hnd, hfree⟩ := he
    have hnot : t ∉ w.committedTids := fun h => by simp [hd t h] at hnd
    simp only [World.step]
    split
    · exact ⟨hc, hp, hl, hz, hd⟩
    · rename_i r hr
      split
      · exact ⟨hc, hp, hl, hz, hd⟩
      · rename_i r' _
        -- The version `r` the update worked on, against the committed row.
        have hbase : ∃ rc, w.committed k = some rc ∧ m r = m rc + w.added t k := by
          unfold World.latest at hr
          split at hr
          · exact hp t k r (by assumption) hr
          · rename_i hnl
            refine ⟨r, hr, ?_⟩
            rw [hz t k hnd hnl]; simp
        obtain ⟨rc, hrc, hm⟩ := hbase
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · intro k' r'' h
          obtain ⟨r0, h0, hm0⟩ := hc k' r'' h
          refine ⟨r0, h0, ?_⟩
          have hf := committedAdded_frozen (w := w)
            (added' := upd w.added t (upd (w.added t) k (w.added t k + (m r' - m r)))) t hnot
            (fun u hu => upd_other _ _ hu) k'
          simp only [World.committedAdded] at hf hm0 ⊢
          rw [hm0, hf]
        · intro t' k' r'' hlk hpk
          by_cases hk : k' = k
          · subst hk
            simp at hlk; subst hlk
            simp at hpk; subst hpk
            refine ⟨rc, hrc, ?_⟩
            simp; omega
          · simp only [upd_other _ _ hk] at hlk
            by_cases ht : t' = t
            · subst ht
              simp [upd_other _ _ hk] at hpk ⊢
              exact hp _ _ _ hlk hpk
            · simp [upd_other _ _ ht] at hpk ⊢
              exact hp _ _ _ hlk hpk
        · intro t' k' hlk
          by_cases hk : k' = k
          · subst hk
            simp at hlk; subst hlk
            simp [hnd]
          · simp only [upd_other _ _ hk] at hlk
            by_cases ht : t' = t
            · subst ht; simp [upd_other _ _ hk, (hl _ _ hlk).1, (hl _ _ hlk).2]
            · simp [upd_other _ _ ht, (hl _ _ hlk).1, (hl _ _ hlk).2]
        · intro t' k' hnd' hnl'
          by_cases ht : t' = t
          · subst ht
            by_cases hk : k' = k
            · subst hk; simp at hnl'
            · simp [upd_other _ _ hk]
              exact hz _ _ hnd' (by simpa [upd_other _ _ hk] using hnl')
          · simp [upd_other _ _ ht]
            by_cases hk : k' = k
            · subst hk
              simp at hnl'
              exact hz _ _ hnd' (by
                intro h
                cases hfree with
                | inl h' => rw [h'] at h; cases h
                | inr h' => rw [h'] at h; cases h; exact hnl' rfl)
            · exact hz _ _ hnd' (by simpa [upd_other _ _ hk] using hnl')
        · intro u hu; exact hd u hu
  | commit t =>
    have hnd : w.done t = false := he
    have hnot : t ∉ w.committedTids := fun h => by simp [hd t h] at hnd
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro k r h
      simp only [World.step] at h
      have hsum : (World.step m w (.commit t)).committedAdded k = w.committedAdded k + w.added t k := by
        simp [World.step, World.committedAdded, List.sum_append]
      rw [hsum]
      split at h
      · rename_i hlk
        obtain ⟨rc, hrc, hm⟩ := hp t k r hlk h
        obtain ⟨r0, h0, hm0⟩ := hc k rc hrc
        exact ⟨r0, h0, by omega⟩
      · rename_i hlk
        obtain ⟨r0, h0, hm0⟩ := hc k r h
        refine ⟨r0, h0, ?_⟩
        rw [hz t k hnd hlk]; omega
    · intro t' k r hlk hpk
      simp only [World.step] at hlk hpk ⊢
      split at hlk
      · cases hlk
      · rename_i hne
        obtain ⟨rc, hrc, hm⟩ := hp t' k r hlk hpk
        refine ⟨rc, ?_, hm⟩
        simp [hne, hrc]
    · intro t' k hlk
      simp only [World.step] at hlk ⊢
      split at hlk
      · cases hlk
      · have ht : t' ≠ t := fun h => by subst h; contradiction
        simp [upd_other _ _ ht, (hl _ _ hlk).1, (hl _ _ hlk).2]
    · intro t' k hnd' hnl'
      simp only [World.step] at hnd' hnl' ⊢
      by_cases ht : t' = t
      · subst ht; simp at hnd'
      · rw [upd_other _ _ ht] at hnd'
        apply hz _ _ hnd'
        intro h
        apply hnl'
        simp [h, ht]
    · intro u hu
      simp only [World.step] at hu ⊢
      rcases List.mem_append.mp hu with hu | hu
      · by_cases ht : u = t
        · subst ht; simp
        · rw [upd_other _ _ ht]; exact hd u hu
      · simp at hu; subst hu; simp
  | abort t =>
    have hnd : w.done t = false := he
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro k r h
      obtain ⟨r0, h0, hm0⟩ := hc k r h
      exact ⟨r0, h0, hm0⟩
    · intro t' k r hlk hpk
      simp only [World.step] at hlk hpk ⊢
      split at hlk
      · cases hlk
      · exact hp t' k r hlk hpk
    · intro t' k hlk
      simp only [World.step] at hlk ⊢
      split at hlk
      · cases hlk
      · have ht : t' ≠ t := fun h => by subst h; contradiction
        simp [upd_other _ _ ht, (hl _ _ hlk).1, (hl _ _ hlk).2]
    · intro t' k hnd' hnl'
      simp only [World.step] at hnd' hnl' ⊢
      by_cases ht : t' = t
      · subst ht; simp at hnd'
      · rw [upd_other _ _ ht] at hnd'
        apply hz _ _ hnd'
        intro h
        apply hnl'
        simp [h, ht]
    · intro u hu
      simp only [World.step] at hu ⊢
      by_cases ht : u = t
      · subst ht; simp
      · rw [upd_other _ _ ht]; exact hd u hu

theorem acct_run (m : Row → Int) (init : Key → Option Row) :
    ∀ (steps : List (Step Key Row)) (w : World Key Row), Runs m w steps → Acct m init w →
      Acct m init (run m w steps) := by
  intro steps
  induction steps with
  | nil => intro w _ ha; exact ha
  | cons s ss ih =>
    intro w hr ha
    exact ih _ hr.2 (acct_step hr.1 ha)

/-- **No lost updates.** In every interleaving of transactions that starts
from `rows`, each committed row's measure is its first measure plus what every
committed transaction added to it. No committed transaction's update is lost
or counted twice, and an aborted transaction adds nothing. -/
theorem no_lost_updates (m : Row → Int) (rows : Key → Option Row) (steps : List (Step Key Row))
    (hr : Runs m (World.init rows) steps) (k : Key) (r : Row)
    (h : (run m (World.init rows) steps).committed k = some r) :
    ∃ r0, rows k = some r0 ∧
      m r = m r0 + (((run m (World.init rows) steps).committedTids.map
        fun t => (run m (World.init rows) steps).added t k).sum) :=
  (acct_run m rows steps _ hr (acct_init m rows)).1 k r h

end tolean.Pg.ReadCommitted
