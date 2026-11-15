import tolean.TypeScript.Spec.RegExp
import tolean.TypeScript.Edition

/-!
The flagless Pattern grammar of ECMA-262 §22.2.1, restricted to the
constructs represented by `JSRegExp.Pattern`. The TypeScript literal reader
keeps escapes intact, and this parser interprets them over UTF-16 code units.
-/
namespace tolean.TypeScript.Syntax.RegExp
open JSRegExp

structure Cursor where
  rest : List UInt16
  captures : Nat := 0
deriving Inhabited

structure ClassAtom where
  ranges : List (UInt16 × UInt16)
  single : Option UInt16 := none

def singleton (u : UInt16) : ClassAtom := ⟨[(u, u)], some u⟩
def digit (u : UInt16) : Bool := 48 ≤ u && u ≤ 57
def hex (u : UInt16) : Option Nat :=
  if digit u then some (u.toNat - 48)
  else if 65 ≤ u && u ≤ 70 then some (u.toNat - 55)
  else if 97 ≤ u && u ≤ 102 then some (u.toNat - 87)
  else none

def readHex : Nat → List UInt16 → Nat → Except String (UInt16 × List UInt16)
  | 0, rest, value => .ok (value.toUInt16, rest)
  | n + 1, c :: cs, value =>
    match hex c with
    | some d => readHex n cs (16 * value + d)
    | none => .error "invalid hexadecimal regular expression escape"
  | _ + 1, [], _ => .error "incomplete hexadecimal regular expression escape"

/-- Complement sorted, disjoint code-unit intervals. Only the fixed classes
below call this helper; arbitrary user classes use the model's negation. -/
def complement (lo : Nat) : List (UInt16 × UInt16) → List (UInt16 × UInt16)
  | [] => if lo ≤ 65535 then [(lo.toUInt16, 65535)] else []
  | (a, b) :: rest =>
    (if lo < a.toNat then [(lo.toUInt16, (a.toNat - 1).toUInt16)] else []) ++
      complement (b.toNat + 1) rest

/-- WhiteSpace and LineTerminator. ES2015 uses Unicode 5.1, in which U+180E
is still a space. ES2016 and later exclude it. -/
def spaces (target : Edition) : List (UInt16 × UInt16) :=
  [(9, 13), (32, 32), (160, 160), (5760, 5760)] ++
    (if target == .es2015 then [(6158, 6158)] else []) ++
    [(8192, 8202), (8232, 8233), (8239, 8239), (8287, 8287),
     (12288, 12288), (65279, 65279)]

def escape (target : Edition) (inClass : Bool) (rest : List UInt16) :
    Except String (ClassAtom × List UInt16) := do
  let c :: cs := rest | throw "unterminated regular expression escape"
  if c == 100 || c == 68 then
    let ranges := [(48, 57)]
    return (⟨if c == 68 then complement 0 ranges else ranges, none⟩, cs)
  if c == 119 || c == 87 then
    let ranges := [(48, 57), (65, 90), (95, 95), (97, 122)]
    return (⟨if c == 87 then complement 0 ranges else ranges, none⟩, cs)
  if c == 115 || c == 83 then
    let ranges := spaces target
    return (⟨if c == 83 then complement 0 ranges else ranges, none⟩, cs)
  if c == 120 || c == 117 then
    let (value, after) ← readHex (if c == 120 then 2 else 4) cs 0
    return (singleton value, after)
  if c == 48 then
    if cs.head?.any digit then throw "legacy octal regular expression escapes are not supported"
    return (singleton 0, cs)
  if digit c then throw "regular expression backreferences are not supported"
  if c == 98 then
    if inClass then return (singleton 8, cs)
    throw "word-boundary assertions are not supported"
  if c == 110 then return (singleton 10, cs)
  if c == 114 then return (singleton 13, cs)
  if c == 116 then return (singleton 9, cs)
  if c == 102 then return (singleton 12, cs)
  if c == 118 then return (singleton 11, cs)
  if ([94, 36, 92, 46, 42, 43, 63, 40, 41, 91, 93, 123, 125, 124, 47, 45] : List UInt16).contains c then
    return (singleton c, cs)
  throw "unsupported regular expression escape"

def classAtom (target : Edition) (rest : List UInt16) :
    Except String (ClassAtom × List UInt16) := do
  let c :: cs := rest | throw "unterminated regular expression character class"
  if c == 92 then escape target true cs else return (singleton c, cs)

def readClass (target : Edition) : Nat → List UInt16 → List (UInt16 × UInt16) →
    Except String (List (UInt16 × UInt16) × List UInt16)
  | 0, _, _ => .error "regular expression parser exhausted its budget"
  | fuel + 1, rest, ranges => do
    let c :: cs := rest | throw "unterminated regular expression character class"
    if c == 93 then return (ranges, cs)
    let (a, after) ← classAtom target rest
    match after with
    | 45 :: endChar :: afterDash =>
      if endChar == 93 then readClass target fuel after (ranges ++ a.ranges)
      else
        let (b, afterRange) ← classAtom target (endChar :: afterDash)
        let some lo := a.single | throw "a character-class range needs literal endpoints"
        let some hi := b.single | throw "a character-class range needs literal endpoints"
        if lo > hi then throw "a character-class range is out of order"
        readClass target fuel afterRange (ranges ++ [(lo, hi)])
    | _ => readClass target fuel after (ranges ++ a.ranges)

def decimal : List UInt16 → Nat → Nat × List UInt16
  | [], n => (n, [])
  | c :: cs, n => if digit c then decimal cs (10 * n + c.toNat - 48) else (n, c :: cs)

def bound (rest : List UInt16) : Except String (Nat × List UInt16) :=
  if rest.head?.any digit then .ok (decimal rest 0)
  else .error "a repetition bound needs decimal digits"

def quantify (p : Pattern) (allowed : Bool) (s : Cursor) : Except String (Pattern × Cursor) := do
  let some c := s.rest.head? | return (p, s)
  if !([42, 43, 63, 123] : List UInt16).contains c then return (p, s)
  if !allowed then throw "regular expression assertions cannot be quantified"
  let (minimum, maximum, after) ←
    if c == 42 then pure (0, none, s.rest.tail)
    else if c == 43 then pure (1, none, s.rest.tail)
    else if c == 63 then pure (0, some 1, s.rest.tail)
    else do
      let (minimum, afterMin) ← bound s.rest.tail
      match afterMin with
      | 125 :: rest => pure (minimum, some minimum, rest)
      | 44 :: 125 :: rest => pure (minimum, none, rest)
      | 44 :: rest =>
        let (maximum, afterMax) ← bound rest
        let 125 :: rest := afterMax | throw "unterminated regular expression quantifier"
        if maximum < minimum then throw "a repetition maximum is smaller than its minimum"
        pure (minimum, some maximum, rest)
      | _ => throw "invalid regular expression quantifier"
  if after.head? == some 63 then throw "lazy regular expression quantifiers are not supported"
  return (.repeat p minimum maximum, { s with rest := after })

mutual
def alternatives (target : Edition) : Nat → Cursor → Except String (Pattern × Cursor)
  | 0, _ => .error "regular expression parser exhausted its budget"
  | fuel + 1, s => do
    let (left, after) ← sequence target fuel .empty s
    if after.rest.head? == some 124 then
      let (right, final) ← alternatives target fuel { after with rest := after.rest.tail }
      return (.alt left right, final)
    return (left, after)

def sequence (target : Edition) : Nat → Pattern → Cursor → Except String (Pattern × Cursor)
  | 0, _, _ => .error "regular expression parser exhausted its budget"
  | fuel + 1, acc, s => do
    if s.rest.isEmpty || s.rest.head? == some 124 || s.rest.head? == some 41 then return (acc, s)
    let (p, quantifiable, after) ← atom target fuel s
    let (p, after) ← quantify p quantifiable after
    sequence target fuel (.seq acc p) after

def atom (target : Edition) : Nat → Cursor → Except String (Pattern × Bool × Cursor)
  | 0, _ => .error "regular expression parser exhausted its budget"
  | fuel + 1, s => do
    let c :: cs := s.rest | throw "expected a regular expression atom"
    if c == 40 then
      let (capturing, rest) ←
        if cs.head? == some 63 then
          match cs with
          | 63 :: 58 :: rest => pure (false, rest)
          | _ => throw "lookaround and named regular expression groups are not supported"
        else pure (true, cs)
      let (p, after) ← alternatives target fuel
        ⟨rest, s.captures + if capturing then 1 else 0⟩
      let 41 :: rest := after.rest | throw "unterminated regular expression group"
      return (if capturing then .capture s.captures p else p, true, { after with rest })
    if c == 91 then
      let negated := cs.head? == some 94
      let (ranges, rest) ← readClass target fuel (if negated then cs.tail else cs) []
      return (.charClass negated ranges, true, { s with rest })
    if c == 92 then
      let (a, rest) ← escape target false cs
      return (.charClass false a.ranges, true, { s with rest })
    if c == 46 then return (.dot, true, { s with rest := cs })
    if c == 94 then return (.beginInput, false, { s with rest := cs })
    if c == 36 then return (.endInput, false, { s with rest := cs })
    if ([42, 43, 63, 123, 125, 93] : List UInt16).contains c then
      throw "unmatched regular expression delimiter or quantifier"
    if c == 10 || c == 13 || c == 0x2028 || c == 0x2029 then
      throw "line break in regular expression literal"
    return (.unit c, true, { s with rest := cs })
end

/-- Parse a pattern body. Exhaustion is an explicit refusal, never a
successful parse or a failed match. -/
def parse (source : String) (target : Edition := .default) : Except String (Pattern × Nat) := do
  let units := (JSString.ofString source).units
  let (p, after) ← alternatives target (10 * (units.length + 1)) ⟨units, 0⟩
  if !after.rest.isEmpty then throw "unmatched regular expression closing parenthesis"
  return (p, after.captures)

end tolean.TypeScript.Syntax.RegExp
