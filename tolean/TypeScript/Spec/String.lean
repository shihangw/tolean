/-!
The model of a JS `string` that `tolean` translates to.

ECMA-262 defines a string as a sequence of 16-bit code units (§6.1.4, the
String type). Text holds UTF-16, so a character above U+FFFF takes two code
units, a surrogate pair. A string may also hold a lone surrogate, a code unit
in the range D800 to DFFF that is not part of a pair.

A Lean `String` cannot be the model. It holds Unicode scalar values, so it
has no lone surrogates, and it measures and orders text by code point. For
example, U+FFFF sorts after U+10000 in JavaScript, because U+10000 starts
with the code unit D800, but in Lean it sorts before it. So the model is the
definition in the spec: `JSString` holds a list of code units. Each string
operation becomes a function on that list, written from its algorithm in the
spec, and a proof uses the lemmas about `List`.

A string literal becomes `JSString.ofString "abc"`, which encodes the text as
UTF-16. `ofString` is injective (`ofString_inj`), so a claim can state a
literal as a Lean `String`, and `simp` can tell two literals apart.

Editions: every edition Tolean supports (`tolean.TypeScript.Edition`). The
String type has been a sequence of 16-bit values since the first edition.
-/
namespace tolean.TypeScript

/-- A JS string: its UTF-16 code units, in order (ECMA-262 §6.1.4). -/
structure JSString where
  units : List UInt16
deriving DecidableEq, Repr, Inhabited

namespace JSString

/-- The code units of one code point, by UTF16EncodeCodePoint (ECMA-262
§11.1.1). A code point up to U+FFFF is one code unit. A larger one is a high
surrogate and then a low surrogate. -/
def utf16 (c : Char) : List UInt16 :=
  let v := c.toNat
  if v < 0x10000 then [v.toUInt16]
  else [(0xD800 + (v - 0x10000) / 0x400).toUInt16, (0xDC00 + (v - 0x10000) % 0x400).toUInt16]

/-- The string that a Lean `String` encodes as UTF-16, as StringToCodePoints
reads it back (ECMA-262 §11.1.4). -/
def ofString (s : String) : JSString := ⟨s.toList.flatMap utf16⟩

instance : Coe String JSString := ⟨ofString⟩

/-- The string has no code units. ToBoolean is false on it (ECMA-262 §7.1.2). -/
def isEmpty (s : JSString) : Bool := s.units.isEmpty

/-- The code points of a list of code units, by CodePointAt (ECMA-262
§11.1.4): a high surrogate and then a low surrogate make one code point. A
lone surrogate becomes U+FFFD. -/
def decode : List UInt16 → List Char
  | [] => []
  | [u] => [unit u]
  | u :: l :: rest =>
    if 0xD800 ≤ u.toNat ∧ u.toNat < 0xDC00 ∧ 0xDC00 ≤ l.toNat ∧ l.toNat < 0xE000 then
      Char.ofNat (0x10000 + (u.toNat - 0xD800) * 0x400 + (l.toNat - 0xDC00)) :: decode rest
    else unit u :: decode (l :: rest)
where
  /-- One code unit that is not part of a pair. -/
  unit (u : UInt16) : Char :=
    if 0xD800 ≤ u.toNat ∧ u.toNat < 0xE000 then '�' else Char.ofNat u.toNat

private theorem decode_cons {u : UInt16} (h : ¬(0xD800 ≤ u.toNat ∧ u.toNat < 0xDC00)) (rest : List UInt16) :
    decode (u :: rest) = decode.unit u :: decode rest := by
  cases rest with
  | nil => rfl
  | cons l rest => simp only [decode]; rw [if_neg (by omega)]

/-- The string as a Lean `String`, with each lone surrogate as U+FFFD. The
interpreter prints a result with it. -/
def toString (s : JSString) : String := String.ofList (decode s.units)

private theorem toNat_toUInt16 {n : Nat} (h : n < 0x10000) : n.toUInt16.toNat = n := by
  simp [Nat.toUInt16, Nat.mod_eq_of_lt h]

private theorem decode_utf16_append (c : Char) (rest : List UInt16) :
    decode (utf16 c ++ rest) = c :: decode rest := by
  have hc := c.valid
  simp only [UInt32.isValidChar, Nat.isValidChar] at hc ⊢
  have hval : c.val.toNat = c.toNat := rfl
  unfold utf16
  by_cases h : c.toNat < 0x10000
  · have hs : ¬(0xD800 ≤ c.toNat ∧ c.toNat < 0xE000) := by
      rw [← hval]; omega
    simp only [h, if_true, List.singleton_append]
    rw [decode_cons (by rw [toNat_toUInt16 h]; omega), decode.unit, toNat_toUInt16 h,
      if_neg hs, Char.ofNat_toNat]
  · have hlt : c.toNat < 0x110000 := by rw [← hval]; omega
    have hhi : 0xD800 + (c.toNat - 0x10000) / 0x400 < 0x10000 := by omega
    have hlo : 0xDC00 + (c.toNat - 0x10000) % 0x400 < 0x10000 := by omega
    simp only [h, if_false, List.cons_append, List.nil_append, decode, toNat_toUInt16 hhi,
      toNat_toUInt16 hlo]
    rw [if_pos (by omega)]
    have hv : 0x10000 + (0xD800 + (c.toNat - 0x10000) / 0x400 - 0xD800) * 0x400 +
        (0xDC00 + (c.toNat - 0x10000) % 0x400 - 0xDC00) = c.toNat := by omega
    rw [hv, Char.ofNat_toNat]

theorem decode_flatMap_utf16 (cs : List Char) : decode (cs.flatMap utf16) = cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih => rw [List.flatMap_cons, decode_utf16_append, ih]

@[simp] theorem toString_ofString (s : String) : (ofString s).toString = s := by
  simp [toString, ofString, decode_flatMap_utf16]

/-- Two literals give the same string exactly when they are the same text. -/
@[simp] theorem ofString_inj {a b : String} : ofString a = ofString b ↔ a = b := by
  constructor
  · intro h
    have := congrArg toString h
    simpa using this
  · intro h; rw [h]

/-- IsLessThan on two lists of code units (ECMA-262 §7.2.13, step 3): the
first code unit where the lists differ decides, and when one list is a prefix
of the other, the shorter one is less. -/
def unitsLt : List UInt16 → List UInt16 → Bool
  | cx :: px, cy :: py => if cx < cy then true else if cy < cx then false else unitsLt px py
  | [], _ :: _ => true
  | _, [] => false

/-- `a < b` on two strings, by IsLessThan (ECMA-262 §7.2.13). It compares
code units, not code points, so U+FFFF is greater than U+10000, which starts
with the code unit D800. -/
def lt (a b : JSString) : Bool := unitsLt a.units b.units

/-- `a <= b` on two strings: `b < a` is false (ECMA-262 §13.10.1). IsLessThan
never gives `undefined` on two strings, so this is all of the rule. -/
def le (a b : JSString) : Bool := !lt b a

/-- `unitsLt` is Lean's lexicographic order on lists of code units. -/
theorem unitsLt_iff (a b : List UInt16) : unitsLt a b = true ↔ a < b := by
  induction a generalizing b with
  | nil => cases b <;> simp [unitsLt, List.nil_lt_cons, List.not_lt_nil]
  | cons x xs ih =>
    cases b with
    | nil => simp [unitsLt, List.not_lt_nil]
    | cons y ys =>
      rw [List.cons_lt_cons_iff, unitsLt, ← ih]
      by_cases hxy : x < y
      · simp [hxy]
      · by_cases hyx : y < x
        · have hne : x ≠ y := by rintro rfl; exact hxy hyx
          simp [hxy, hyx, hne]
        · have heq : x = y := by
            simp only [UInt16.lt_iff_toNat_lt] at hxy hyx
            exact UInt16.toNat_inj.mp (by omega)
          simp [heq]

/-- `a < b` on strings is Lean's lexicographic order on their code units. A
claim can use the lemmas about `List.lt` with it. -/
theorem lt_iff (a b : JSString) : a.lt b = true ↔ a.units < b.units := unitsLt_iff _ _

/-- `a <= b` on strings is Lean's `≤` on their code units. -/
theorem le_iff (a b : JSString) : a.le b = true ↔ a.units ≤ b.units := by
  rw [← List.not_lt, ← lt_iff]
  simp [le]

end JSString

end tolean.TypeScript
