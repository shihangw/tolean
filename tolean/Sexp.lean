import tolean.Source

/-!
The S-expression form of a syntax tree. The parsers print it, and the tests
compare it line by line with what a reference parser (such as `tsc`) gives
for the same file.

One node per line:

```
(binary 1:1-1:6 +
  (ident 1:1-1:2 a)
  (ident 1:5-1:6 b))
```

The head names the node kind. The span follows, then the atoms (names,
operators, flags, literal text), then the child nodes, one per line.
-/
namespace tolean

inductive Sexp where
  | node (head : String) (span : Option Span) (atoms : List String) (children : List Sexp)
deriving Inhabited

/-- A string as `JSON.stringify` writes it, so that the reference printer in
JavaScript gives the same text. -/
def Sexp.quote (s : String) : String :=
  let body := s.foldl (init := "") fun acc c =>
    match c with
    | '"' => acc ++ "\\\""
    | '\\' => acc ++ "\\\\"
    | '\n' => acc ++ "\\n"
    | '\r' => acc ++ "\\r"
    | '\t' => acc ++ "\\t"
    | _ =>
      if c.toNat == 0x08 then acc ++ "\\b"
      else if c.toNat == 0x0C then acc ++ "\\f"
      else if c.toNat < 0x20 then acc ++ "\\u" ++ hexDigits c.toNat 4
      else acc.push c
  "\"" ++ body ++ "\""

partial def Sexp.render (s : Sexp) (indent : Nat := 0) : String :=
  match s with
  | .node head span atoms children =>
    let first := " ".intercalate (head :: (span.map Span.render).toList ++ atoms)
    let rest := children.foldl (init := "") fun acc child =>
      acc ++ "\n" ++ "".pushn ' ' (indent + 2) ++ child.render (indent + 2)
    "(" ++ first ++ rest ++ ")"

end tolean
