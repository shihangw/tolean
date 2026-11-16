import tolean.TypeScript.Spec.String

/-!
Ordered, greedy matching without flags, following ECMA-262 §22.2.2.
Positions count UTF-16 code units. A continuation decides whether the part
after a candidate match succeeds, so an alternative can backtrack when it
fails. Flagless literals and their `test` method use this model.
-/
namespace tolean.TypeScript.JSRegExp

structure State (length : Nat) where
  pos : Fin (length + 1)
  captures : List (Option (Nat × Nat)) := []

abbrev Continuation (length : Nat) := State length → Option (State length)
abbrev Matcher (length : Nat) := State length → Continuation length → Option (State length)

/-- RepeatMatcher (§22.2.2.3.1). An empty iteration can decrease a positive
minimum. Once the minimum is zero, an iteration must advance. The extra
backwards guard makes this helper total even for an arbitrary atom.
`repeat_spec_step` proves that the guard has no effect on forward atoms. -/
def repeatMatch {length : Nat} (atom : Matcher length)
    (clear : State length → State length) (minimum : Nat) (maximum : Option Nat)
    (s : State length) (k : Continuation length) : Option (State length) :=
  if maximum == some 0 then
    if minimum == 0 then k s else none
  else
    let more := atom (clear s) fun next =>
      if hback : next.pos.val < s.pos.val then none
      else if hempty : minimum = 0 ∧ next.pos.val = s.pos.val then none
      else repeatMatch atom clear (minimum - 1) (maximum.map (· - 1)) next k
    more.orElse fun _ => if minimum == 0 then k s else none
termination_by minimum + (length - s.pos.val)
decreasing_by omega

/-- Patterns after their character escapes have been decoded. Captures have
zero-based indices in opening-parenthesis order. A non-capturing group needs
no node: its body has the group's meaning. -/
inductive Pattern where
  | empty
  | unit (value : UInt16)
  | charClass (negated : Bool) (ranges : List (UInt16 × UInt16))
  | dot
  | beginInput
  | endInput
  | seq (left right : Pattern)
  | alt (left right : Pattern)
  | capture (index : Nat) (body : Pattern)
  | repeat (body : Pattern) (minimum : Nat) (maximum : Option Nat)
deriving Repr, Inhabited, BEq, DecidableEq

/-- A compiled flagless literal. The subset never changes `lastIndex` or
observes identity, so `test` needs only the pattern. -/
structure Regex where
  pattern : Pattern
  captureCount : Nat
deriving Repr, Inhabited, BEq, DecidableEq

def Pattern.captureIndices : Pattern → List Nat
  | .seq a b | .alt a b => a.captureIndices ++ b.captureIndices
  | .capture i p => i :: p.captureIndices
  | .repeat p _ _ => p.captureIndices
  | _ => []

/-- RepeatMatcher clears the captures inside its atom before each iteration.
It does not retain a capture from an earlier iteration that a later one
does not participate in. -/
def clearCaptures {length : Nat} (indices : List Nat) (s : State length) : State length :=
  { s with captures := s.captures.mapIdx fun i c => if indices.contains i then none else c }

def one (input : JSString) (accept : UInt16 → Bool) : Matcher input.units.length :=
  fun s k =>
    if h : s.pos.val < input.units.length then
      if accept input.units[s.pos.val] then
        k { s with pos := ⟨s.pos.val + 1, by omega⟩ }
      else none
    else none

/-- CompilePattern's continuation-passing semantics for the subset. Without
`m`, `$` tests only the end of input, not a final line terminator. Without
`s`, dot excludes all four ECMAScript line terminators. -/
def compile (input : JSString) : Pattern → Matcher input.units.length
  | .empty => fun s k => k s
  | .unit u => one input (· == u)
  | .charClass negated ranges =>
    one input fun u => (ranges.any fun (lo, hi) => lo ≤ u && u ≤ hi) != negated
  | .dot => one input fun u => !(u == 10 || u == 13 || u == 0x2028 || u == 0x2029)
  | .beginInput => fun s k => if s.pos.val == 0 then k s else none
  | .endInput => fun s k => if s.pos.val == input.units.length then k s else none
  | .seq a b => fun s k => compile input a s (fun next => compile input b next k)
  | .alt a b => fun s k => (compile input a s k).orElse fun _ => compile input b s k
  | .capture i p => fun s k =>
    compile input p s fun next =>
      k { next with captures := next.captures.set i (some (s.pos.val, next.pos.val)) }
  | .repeat p minimum maximum =>
    repeatMatch (compile input p) (clearCaptures p.captureIndices) minimum maximum

/-- Search starting positions in order, including the end of the input.
The caller supplies one capture slot for each capturing group. -/
def search (input : JSString) (p : Pattern) (captureCount : Nat) :
    Option (Nat × State input.units.length) :=
  (List.finRange (input.units.length + 1)).findSome? fun start =>
    let s : State input.units.length := ⟨start, List.replicate captureCount none⟩
    (compile input p s some).map (start.val, ·)

/-- RegExp.prototype.test (§22.2.6.16), without global or sticky state.
Captures cannot affect success in the fragment without backreferences. -/
def test (input : JSString) (p : Pattern) : Bool :=
  (search input p 0).isSome

def Regex.test (r : Regex) (input : JSString) : Bool :=
  JSRegExp.test input r.pattern

/-- The first replacement, without dollar substitutions or callbacks
(ECMA-262 §22.2.6.11). Captures affect the search but not this replacement. -/
def Regex.replaceLiteral (r : Regex) (input replacement : JSString) : JSString :=
  match search input r.pattern r.captureCount with
  | none => input
  | some (start, state) =>
    ⟨input.units.take start ++ replacement.units ++ input.units.drop state.pos.val⟩

/-- The matcher invokes its continuation only at positions at or after the
start. The continuation itself may return any state, so a claim about only
the final position would not express this property. -/
def Forward {length : Nat} (m : Matcher length) : Prop :=
  ∀ s k₁ k₂, (∀ next, s.pos.val ≤ next.pos.val → k₁ next = k₂ next) →
    m s k₁ = m s k₂

theorem one_forward (input : JSString) (accept : UInt16 → Bool) :
    Forward (one input accept) := by
  intro s k₁ k₂ h
  unfold one
  split
  · split
    · apply h
      change s.pos.val ≤ s.pos.val + 1
      omega
    · rfl
  · rfl

theorem repeat_forward {length : Nat} (atom : Matcher length)
    (clear : State length → State length) (hc : ∀ s, (clear s).pos = s.pos)
    (ha : Forward atom) (minimum : Nat) (maximum : Option Nat)
    (s : State length) (k₁ k₂ : Continuation length)
    (hk : ∀ next, s.pos.val ≤ next.pos.val → k₁ next = k₂ next) :
    repeatMatch atom clear minimum maximum s k₁ =
      repeatMatch atom clear minimum maximum s k₂ := by
  rw [repeatMatch, repeatMatch]
  split
  · split <;> first | exact hk s (Nat.le_refl _) | rfl
  · dsimp only
    congr 1
    · apply ha
      intro next hn
      split
      · rfl
      · split
        · rfl
        · apply repeat_forward atom clear hc ha
          intro final hf
          apply hk
          rw [hc] at hn
          exact Nat.le_trans hn hf
    · funext _
      split
      · exact hk s (Nat.le_refl _)
      · rfl
termination_by minimum + (length - s.pos.val)
decreasing_by omega

theorem compile_forward (input : JSString) (p : Pattern) : Forward (compile input p) := by
  induction p with
  | empty =>
    intro s k₁ k₂ hk
    exact hk s (Nat.le_refl _)
  | unit u => exact one_forward input _
  | charClass negated ranges => exact one_forward input _
  | dot => exact one_forward input _
  | beginInput =>
    intro s k₁ k₂ hk
    simp only [compile]
    split
    · exact hk s (Nat.le_refl _)
    · rfl
  | endInput =>
    intro s k₁ k₂ hk
    simp only [compile]
    split
    · exact hk s (Nat.le_refl _)
    · rfl
  | seq a b ha hb =>
    intro s k₁ k₂ hk
    apply ha
    intro next hn
    apply hb
    intro final hf
    exact hk final (Nat.le_trans hn hf)
  | alt a b ha hb =>
    intro s k₁ k₂ hk
    simp only [compile]
    rw [ha s k₁ k₂ hk, hb s k₁ k₂ hk]
  | capture i p hp =>
    intro s k₁ k₂ hk
    apply hp
    intro next hn
    exact hk _ hn
  | «repeat» p minimum maximum hp =>
    intro s k₁ k₂ hk
    exact repeat_forward _ (clearCaptures p.captureIndices) (fun _ => rfl) hp minimum maximum s k₁ k₂ hk

/-- The termination guard is observationally absent for a forward atom.
The right side is RepeatMatcher's greedy step with its empty-match check. -/
theorem repeat_spec_step {length : Nat} (atom : Matcher length)
    (clear : State length → State length) (hc : ∀ s, (clear s).pos = s.pos)
    (ha : Forward atom) (minimum : Nat) (maximum : Option Nat)
    (s : State length) (k : Continuation length) :
    repeatMatch atom clear minimum maximum s k =
      if maximum == some 0 then
        if minimum == 0 then k s else none
      else
        (atom (clear s) fun next =>
          if minimum = 0 ∧ next.pos.val = s.pos.val then none
          else repeatMatch atom clear (minimum - 1) (maximum.map (· - 1)) next k).orElse
          (fun _ => if minimum == 0 then k s else none) := by
  rw [repeatMatch]
  split
  · rfl
  · dsimp only
    congr 1
    apply ha
    intro next hn
    rw [hc] at hn
    simp only [show ¬next.pos.val < s.pos.val by omega, dite_false]
    split <;> simp_all

end tolean.TypeScript.JSRegExp
