import tolean.TypeScript.Spec.String

namespace tolean.TypeScript

/-- An array-index property name in OrdinaryOwnPropertyKeys (ECMA-262
§10.1.11.1). The upper bound excludes 2^32 - 1, and the round trip excludes
leading zeroes, signs and whitespace. -/
def recordArrayIndex (key : String) : Option Nat := do
  let n ← key.toNat?
  if n < 4294967295 && toString n == key then some n else none

/-- Insert a property among the array-index properties without changing the
relative order of the other properties. -/
def insertRecordEntry {V : Type} (entry : String × V) :
    List (String × V) → List (String × V)
  | [] => [entry]
  | head :: tail =>
    match recordArrayIndex entry.1, recordArrayIndex head.1 with
    | some i, some j =>
      if i ≤ j then entry :: head :: tail else head :: insertRecordEntry entry tail
    | some _, none => entry :: head :: tail
    | none, _ => head :: insertRecordEntry entry tail

/-- OrdinaryOwnPropertyKeys for string properties: array indices come first
in ascending order. The other properties retain their insertion order. -/
def orderedRecordEntries {V : Type} (entries : List (String × V)) : List (String × V) :=
  entries.foldl (fun acc entry => insertRecordEntry entry acc) []

/-- A string-keyed record retains the order in which its literal wrote its
properties. Lookup compares UTF-16 code units rather than decoding the key. -/
structure JSRecord (V : Type) where
  fields : List (String × V)
deriving Repr, Inhabited

namespace JSRecord

def get? {V : Type} (record : JSRecord V) (key : JSString) : Option V :=
  (record.fields.find? fun entry => JSString.ofString entry.1 == key).map (·.2)

def hasOwn {V : Type} (record : JSRecord V) (key : JSString) : Bool :=
  (record.get? key).isSome

def entries {V : Type} (record : JSRecord V) : List (JSString × V) :=
  (orderedRecordEntries record.fields).map fun (key, value) => (JSString.ofString key, value)

def keys {V : Type} (record : JSRecord V) : List JSString :=
  record.entries.map (·.1)

end JSRecord

end tolean.TypeScript
