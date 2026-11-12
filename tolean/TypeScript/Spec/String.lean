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

/-- `a + b` on two strings: the code units of `a`, then those of `b`
(ApplyStringOrNumericBinaryOperator, ECMA-262 §13.15.3). -/
instance : Append JSString := ⟨fun a b => ⟨a.units ++ b.units⟩⟩

@[simp] theorem units_append (a b : JSString) : (a ++ b).units = a.units ++ b.units := rfl

/-- Two literals joined are the literal of the joined text, so `simp` can
join the literals of a claim. -/
@[simp] theorem ofString_append (a b : String) : ofString a ++ ofString b = ofString (a ++ b) := by
  simp only [ofString, String.toList_append, List.flatMap_append]
  rfl

/-- ToString of a bigint (ECMA-262 §7.1.17): `BigInt::toString` with radix
10 (§6.1.6.2.21). It writes the decimal digits of the value, after `-` when
the value is negative, as Lean's `toString` does on an `Int`. -/
def ofInt (i : Int) : JSString := ofString (ToString.toString i)

/-- ToString of a boolean (ECMA-262 §7.1.17): `"true"` or `"false"`. -/
def ofBool (b : Bool) : JSString := ofString (if b then "true" else "false")

/-- The `length` of a string: the number of its code units (ECMA-262
§22.1.4.1), so a character above U+FFFF counts twice. -/
def length (s : JSString) : Nat := s.units.length

/-- `s.startsWith(p)`, with no position (ECMA-262 §22.1.3.25): the code units
of `p` begin those of `s`. -/
def startsWith (s p : JSString) : Bool := p.units.isPrefixOf s.units

/-- `s.endsWith(p)`, with no end position (ECMA-262 §22.1.3.7): the code units
of `p` end those of `s`. -/
def endsWith (s p : JSString) : Bool := p.units.isSuffixOf s.units

/-- StringIndexOf(s, p, 0) (ECMA-262 §6.1.4.1): the first index at which the
code units of `p` occur in `s`. The empty string occurs at index 0. -/
def indexOf? (s p : JSString) : Option Nat := go s.units 0
where
  /-- The first index, from `i` on, at which `p` occurs in the rest `l`. -/
  go : List UInt16 → Nat → Option Nat
    | l, i =>
      if p.units.isPrefixOf l then some i
      else match l with
        | [] => none
        | _ :: rest => go rest (i + 1)

/-- `s.indexOf(p)`, with no position (ECMA-262 §22.1.3.9): the first index at
which `p` occurs, or -1. -/
def indexOf (s p : JSString) : Int :=
  match indexOf? s p with
  | some i => i
  | none => -1

/-- `s.includes(p)`, with no position (ECMA-262 §22.1.3.8): StringIndexOf
finds `p` in `s`. -/
def includes (s p : JSString) : Bool := (indexOf? s p).isSome

/-- The code points that `trim` removes: WhiteSpace and LineTerminator
(ECMA-262 §12.2 and §12.3). WhiteSpace is TAB, VT, FF, ZWNBSP (U+FEFF) and
every code point of the Unicode category Zs. Zs has had these members since
Unicode 6.3. ES2016 and later name Unicode 8.0 or later, so they agree on
them. ES2015 names Unicode 5.1, where U+180E is in Zs too, so the translator
refuses `trim` for that target. Each of them is one code unit that is not a
surrogate, so a code unit is one of them exactly when the code point that it
starts is. -/
def whiteSpace : List Nat :=
  [0x09, 0x0A, 0x0B, 0x0C, 0x0D, 0x20, 0xA0, 0x1680, 0x2000, 0x2001, 0x2002, 0x2003, 0x2004,
   0x2005, 0x2006, 0x2007, 0x2008, 0x2009, 0x200A, 0x2028, 0x2029, 0x202F, 0x205F, 0x3000, 0xFEFF]

/-- The code unit `u` is white space or a line terminator. -/
def isWhite (u : UInt16) : Bool := whiteSpace.contains u.toNat

/-- `s.trimStart()` (ECMA-262 §22.1.3.34): the string without the white space
at its start, as TrimString removes it. -/
def trimStart (s : JSString) : JSString := ⟨s.units.dropWhile isWhite⟩

/-- `s.trimEnd()` (ECMA-262 §22.1.3.33): the string without the white space at
its end. -/
def trimEnd (s : JSString) : JSString := ⟨(s.units.reverse.dropWhile isWhite).reverse⟩

/-- `s.trim()` (ECMA-262 §22.1.3.32): the string without the white space at
either end. -/
def trim (s : JSString) : JSString := s.trimStart.trimEnd

/-- The pieces of `l` between the occurrences of the separator `c :: cs`, by
the loop of String.prototype.split (ECMA-262 §22.1.3.23, steps 14 to 19).
`piece` holds the code units of the current piece, last first. Each match
skips the separator, so the next search starts after it. -/
def splitUnits (c : UInt16) (cs : List UInt16) : List UInt16 → List UInt16 → List (List UInt16)
  | [], piece => [piece.reverse]
  | u :: rest, piece =>
    if (c :: cs).isPrefixOf (u :: rest) then
      piece.reverse :: splitUnits c cs ((u :: rest).drop (cs.length + 1)) []
    else splitUnits c cs rest (u :: piece)
termination_by l => l.length
decreasing_by all_goals simp only [List.length_drop, List.length_cons]; omega

/-- `s.split(sep)` with a string separator and no limit (ECMA-262 §22.1.3.23).
An empty separator splits `s` into its code units. Otherwise the pieces are the
parts of `s` between the occurrences of `sep`, so the empty string gives one
empty piece. The spec stops at 2^32 - 1 pieces. -/
def split (s sep : JSString) : List JSString :=
  match sep.units with
  | [] => (s.units.take (2 ^ 32 - 1)).map fun u => ⟨[u]⟩
  | c :: cs => ((splitUnits c cs s.units []).take (2 ^ 32 - 1)).map JSString.mk

/-- `startsWith` is Lean's prefix order on the code units. -/
theorem startsWith_iff (s p : JSString) : s.startsWith p = true ↔ p.units <+: s.units :=
  List.isPrefixOf_iff_prefix

/-- `endsWith` is Lean's suffix order on the code units. -/
theorem endsWith_iff (s p : JSString) : s.endsWith p = true ↔ p.units <:+ s.units :=
  List.isSuffixOf_iff_suffix

private theorem indexOf?_go_isSome (p : JSString) (l : List UInt16) (i : Nat) :
    (indexOf?.go p l i).isSome = true ↔ p.units <:+: l := by
  induction l generalizing i with
  | nil =>
    unfold indexOf?.go
    by_cases h : p.units.isPrefixOf [] = true
    · simp only [h, if_true, Option.isSome_some, true_iff]
      exact (List.isPrefixOf_iff_prefix.mp h).isInfix
    · simp only [h, Bool.false_eq_true, if_false, Option.isSome_none, false_iff]
      intro hin
      exact h (List.isPrefixOf_iff_prefix.mpr (List.infix_nil.mp hin ▸ List.nil_prefix))
  | cons x xs ih =>
    unfold indexOf?.go
    by_cases h : p.units.isPrefixOf (x :: xs) = true
    · simp only [h, if_true, Option.isSome_some, true_iff]
      exact (List.isPrefixOf_iff_prefix.mp h).isInfix
    · simp only [h, Bool.false_eq_true, if_false, ih]
      constructor
      · exact fun hin => hin.trans (List.suffix_cons x xs).isInfix
      · intro hin
        rcases List.infix_cons_iff.mp hin with hp | hin
        · exact absurd (List.isPrefixOf_iff_prefix.mpr hp) h
        · exact hin

/-- `includes` is Lean's infix order on the code units. -/
theorem includes_iff (s p : JSString) : s.includes p = true ↔ p.units <:+: s.units :=
  indexOf?_go_isSome p s.units 0

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

/-- Strings compare by their code units, as `<` does. A certificate for a
sort by a string key compares the keys with it. -/
instance : Ord JSString := ⟨fun a b => compare a.units b.units⟩

instance : Std.TransOrd JSString where
  eq_swap {a b} := Std.OrientedCmp.eq_swap (cmp := (compare : List UInt16 → List UInt16 → Ordering))
    (a := a.units) (b := b.units)
  isLE_trans {a b c} := Std.TransCmp.isLE_trans (cmp := (compare : List UInt16 → List UInt16 → Ordering))
    (a := a.units) (b := b.units) (c := c.units)

/-- `unitsLt` is `compare` on lists of code units. -/
theorem unitsLt_compare (a b : List UInt16) : unitsLt a b = true ↔ compare a b = .lt := by
  induction a generalizing b with
  | nil => cases b <;> simp [unitsLt]
  | cons x xs ih =>
    cases b with
    | nil => simp [unitsLt]
    | cons y ys =>
      rw [List.compare_eq_compareLex, List.compareLex_cons_cons, ← List.compare_eq_compareLex, unitsLt]
      by_cases hxy : x < y
      · simp [hxy, Std.compare_eq_lt.mpr hxy, Ordering.then]
      · by_cases hyx : y < x
        · simp [hxy, hyx, Std.compare_eq_gt.mpr hyx, Ordering.then]
        · have heq : x = y := by
            simp only [UInt16.lt_iff_toNat_lt] at hxy hyx
            exact UInt16.toNat_inj.mp (by omega)
          subst heq
          simp [Std.ReflCmp.compare_self, Ordering.then, ih]

theorem compare_of_lt {a b : JSString} (h : a.lt b = true) : compare a b = .lt :=
  (unitsLt_compare a.units b.units).mp h

theorem compare_of_gt {a b : JSString} (h : b.lt a = true) : compare a b = .gt := by
  have := (unitsLt_compare b.units a.units).mp h
  show compare a.units b.units = .gt
  rw [Std.OrientedCmp.eq_swap (cmp := compare) (a := a.units) (b := b.units), this]; rfl

theorem compare_of_eq {a b : JSString} (h1 : ¬a.lt b = true) (h2 : ¬b.lt a = true) :
    compare a b = .eq := by
  show compare a.units b.units = .eq
  cases hc : compare a.units b.units
  · exact absurd ((unitsLt_compare _ _).mpr hc) h1
  · rfl
  · have : compare b.units a.units = .lt := by
      rw [Std.OrientedCmp.eq_swap (cmp := compare) (a := b.units) (b := a.units), hc]; rfl
    exact absurd ((unitsLt_compare _ _).mpr this) h2

end JSString

end tolean.TypeScript
