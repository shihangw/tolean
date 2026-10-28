import tolean.TypeScript.Spec.Eval

/-! ECMA-262 chapter 12, ECMAScript Language: Lexical Grammar. -/
namespace tolean.TypeScript.Coverage

/-! ### §12.9.3 Numeric Literals -/

-- A literal whose digits are all zero is 0, however long its fraction is.
-- The interpreter once refused a zero with more than 400 fraction digits.
#guard Eval.numberLiteral ("0." ++ "".pushn '0' 401) == some 0
-- A fraction with a digit that is not zero leaves the subset, at any length.
#guard Eval.numberLiteral ("0." ++ "".pushn '0' 401 ++ "1") == none

end tolean.TypeScript.Coverage
