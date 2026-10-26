
/-!
Scenarios for checking the generated `Ledger` model against PostgreSQL.
`go run ./pgcheck corpus` appends this file to the translation, runs it with
`TOLEAN_SCENARIOS` set to the output path, and runs the scenarios.
-/
namespace LedgerScenarios

open tolean Ledger

def hex2 (b : UInt8) : String :=
  let d := Nat.toDigits 16 b.toNat
  String.ofList (if d.length < 2 then '0' :: d else d)

def uuidText (u : Pg.UUID) : String :=
  let s := (String.join (u.toList.map hex2)).toList
  let part (a b : Nat) := String.ofList ((s.drop a).take (b - a))
  s!"{part 0 8}-{part 8 12}-{part 12 16}-{part 16 20}-{part 20 32}"

def idOf (n : Nat) : Pg.UUID := Vector.replicate 16 (UInt8.ofNat (n * 17))

def t0 : Pg.Timestamp := ⟨1767225600 * 1000000⟩
def t1 : Pg.Timestamp := ⟨1767312000 * 1000000⟩

def tsLiteral (t : Pg.Timestamp) : String :=
  if t = t0 then "'2026-01-01 00:00:00+00'::timestamptz" else "'2026-01-02 00:00:00+00'::timestamptz"

def tsText (t : Pg.Timestamp) : String :=
  if t = t0 then "2026-01-01 00:00:00+00" else "2026-01-02 00:00:00+00"

def stateText : «account_state» → String
  | .«open» => "open"
  | .«frozen» => "frozen"

structure Account where
  n : Nat
  closed : Bool
  accountState : «account_state»
  balanceState : «account_state»
  amount : Int
  floor : Int

def big : Int := 2 ^ 63 - 1

def states : List (List Account) :=
  [ [⟨1, false, .open, .open, 100, 0⟩, ⟨2, false, .open, .frozen, -50, -100⟩, ⟨3, true, .open, .open, 10, 0⟩],
    [⟨1, false, .frozen, .open, 40, 0⟩, ⟨2, false, .open, .open, -big, -big - 1⟩, ⟨3, false, .open, .open, big - 1, 0⟩],
    [⟨1, true, .frozen, .frozen, 0, 0⟩, ⟨2, false, .open, .open, 7, 9⟩] ]

def dbOf (as : List Account) : DB :=
  { «accounts» := fun k => (as.find? (idOf ·.n = k)).map fun a =>
      { «id» := idOf a.n, «name» := s!"acct{a.n}", «state» := a.accountState,
        «closed_at» := if a.closed then some t0 else none, «extra» := none, «opened_at» := t0,
        «currency» := "" },
    «balances» := fun k => (as.find? (idOf ·.n = k)).map fun a =>
      { «account» := idOf a.n, «amount» := a.amount, «floor_amount» := a.floor, «state» := a.balanceState,
        «posted_at» := t0 } }

def setupOf (as : List Account) : List String :=
  as.flatMap fun a =>
    [s!"INSERT INTO accounts (id, name, state, closed_at, opened_at) VALUES ('{uuidText (idOf a.n)}', 'acct{a.n}', '{stateText a.accountState}', {if a.closed then tsLiteral t0 else "NULL"}, {tsLiteral t0})",
     s!"INSERT INTO balances (account, amount, floor_amount, state, posted_at) VALUES ('{uuidText (idOf a.n)}', {a.amount}, {a.floor}, '{stateText a.balanceState}', {tsLiteral t0})"]

def stateSql : String := "SELECT account, amount, floor_amount, state, posted_at FROM balances ORDER BY account"

def stateRows (db : DB) : List String :=
  [1, 2, 3].filterMap fun n => (db.«balances» (idOf n)).map fun r =>
    s!"{uuidText r.«account»}|{r.«amount»}|{r.«floor_amount»}|{stateText r.«state»}|{tsText r.«posted_at»}"

def errText : Pg.Error → String
  | .outOfRange => "ERROR 22003"
  | .cardinality => "ERROR 21000"
  | .noRows => ""

def jsonStr (s : String) : String :=
  "\"" ++ s.foldl (fun acc c => match c with
    | '"' => acc ++ "\\\""
    | '\\' => acc ++ "\\\\"
    | '\n' => acc ++ "\\n"
    | c => acc.push c) "" ++ "\""

def jsonObj (fields : List (String × String)) : String :=
  "{" ++ ",".intercalate (fields.map fun (k, v) => s!"{jsonStr k}:{v}") ++ "}"

def expectOf {A : Type} (db : DB) (r : Pg.Result (A × DB)) (show_ : A → List String)
    (onError : List String := []) : List String :=
  match r with
  | .ok (v, db') => show_ v ++ ["---state"] ++ stateRows db'
  | .error e => [errText e] ++ onError ++ ["---state"] ++ stateRows db

def scenario (name query kind : String) (args : List (String × String)) (as : List Account)
    (expect : List String) : String :=
  jsonObj [("name", jsonStr name), ("query", jsonStr query), ("kind", jsonStr kind),
    ("args", jsonObj (args.map fun (k, v) => (k, jsonStr v))), ("now", jsonStr (tsLiteral t1)),
    ("setup", "[" ++ ",".intercalate ((setupOf as).map jsonStr) ++ "]"),
    ("state", jsonStr stateSql), ("expect", jsonStr ("\n".intercalate (expect.filter (· != ""))))]

def run : IO Unit := do
  let mut lines := #[]
  for (as, si) in states.zipIdx do
    let db := dbOf as
    for n in [1, 2, 3, 4] do
      let acct := s!"'{uuidText (idOf n)}'"
      let tag := s!"s{si}-a{n}"
      lines := lines.push (scenario s!"freeze-{tag}" "Freeze" "execrows" [("account", acct)] as
        (expectOf db (Freeze t1 (idOf n) db) (fun v => [toString v]) ["0"]))
      lines := lines.push (scenario s!"get-{tag}" "GetAccount" "one" [("account", acct)] as
        (expectOf db (GetAccount t1 (idOf n) db) fun r =>
          [s!"{r.«name»}|{r.«available»}|{r.«state»}|{tsText r.«until»}|{if r.«open» then "t" else "f"}"]))
      for k in [(-5 : Int), 0, 10, 60, 2 ^ 62] do
        lines := lines.push (scenario s!"debit-{tag}-{k}" "Debit" "one" [("account", acct), ("n", toString k)] as
          (expectOf db (Debit t1 (idOf n) k db) fun v => [toString v]))
        lines := lines.push (scenario s!"credit-{tag}-{k}" "Credit" "one" [("account", acct), ("n", toString k)] as
          (expectOf db (Credit t1 (idOf n) k db) fun v => [(v.map toString).getD ""]))
  let some path ← IO.getEnv "TOLEAN_SCENARIOS" | throw (IO.userError "set TOLEAN_SCENARIOS")
  IO.FS.writeFile path ("\n".intercalate lines.toList ++ "\n")

end LedgerScenarios

#eval LedgerScenarios.run
