import tolean.TypeScript.Output

/-!
Equality of output trees, as a function that the kernel can run.

Lean cannot derive `DecidableEq` for `Expr`, which holds lists of itself. So
`Expr.beq` compares two trees field by field, and `Expr.beq_iff` proves that
it is true exactly when the trees are equal. The other output types then
derive `DecidableEq`. A certificate uses this equality to check that the
translator gives the output tree that its theorems are about: the kernel runs
the translator and compares the trees.
-/
namespace tolean.TypeScript.Output

-- Every proof here has the same shape, so some pass a lemma that they do not use.
set_option linter.unusedSimpArgs false

deriving instance DecidableEq for IntOp, Order, Division, NumberOp, NumberConstant, NumberTest, Ty

mutual

def Expr.beq : Expr → Expr → Bool
  | .int a0, .int b0 => Decidable.decide (a0 = b0)
  | .number a0, .number b0 => Decidable.decide (a0 = b0)
  | .numberConstant a0, .numberConstant b0 => Decidable.decide (a0 = b0)
  | .none, .none => true
  | .bool a0, .bool b0 => Decidable.decide (a0 = b0)
  | .string a0, .string b0 => Decidable.decide (a0 = b0)
  | .var a0, .var b0 => Decidable.decide (a0 = b0)
  | .field a0 a1 a2, .field b0 b1 b2 => Expr.beq a0 b0 && Decidable.decide (a1 = b1) && Decidable.decide (a2 = b2)
  | .propNot a0, .propNot b0 => Expr.beq a0 b0
  | .not a0, .not b0 => Expr.beq a0 b0
  | .neg a0, .neg b0 => Expr.beq a0 b0
  | .numberNeg a0, .numberNeg b0 => Expr.beq a0 b0
  | .ite a0 a1 a2, .ite b0 b1 b2 => Expr.beq a0 b0 && Expr.beq a1 b1 && Expr.beq a2 b2
  | .call a0 a1, .call b0 b1 => Decidable.decide (a0 = b0) && Expr.beqList a1 b1
  | .list a0 a1, .list b0 b1 => Expr.beqList a0 b0 && Decidable.decide (a1 = b1)
  | .struct a0 a1, .struct b0 b1 => Expr.beqFields a0 b0 && Decidable.decide (a1 = b1)
  | .isNone a0, .isNone b0 => Expr.beq a0 b0
  | .isSome a0, .isSome b0 => Expr.beq a0 b0
  | .matchNull a0 a1 a2, .matchNull b0 b1 b2 => Decidable.decide (a0 = b0) && Expr.beq a1 b1 && Expr.beq a2 b2
  | .intOp a0 a1 a2, .intOp b0 b1 b2 => Decidable.decide (a0 = b0) && Expr.beq a1 b1 && Expr.beq a2 b2
  | .order a0 a1 a2, .order b0 b1 b2 => Decidable.decide (a0 = b0) && Expr.beq a1 b1 && Expr.beq a2 b2
  | .division a0 a1 a2, .division b0 b1 b2 => Decidable.decide (a0 = b0) && Expr.beq a1 b1 && Expr.beq a2 b2
  | .numberOp a0 a1 a2, .numberOp b0 b1 b2 => Decidable.decide (a0 = b0) && Expr.beq a1 b1 && Expr.beq a2 b2
  | .numberNe a0 a1, .numberNe b0 b1 => Expr.beq a0 b0 && Expr.beq a1 b1
  | .eq a0 a1, .eq b0 b1 => Expr.beq a0 b0 && Expr.beq a1 b1
  | .ne a0 a1, .ne b0 b1 => Expr.beq a0 b0 && Expr.beq a1 b1
  | .propAnd a0 a1, .propAnd b0 b1 => Expr.beq a0 b0 && Expr.beq a1 b1
  | .propOr a0 a1, .propOr b0 b1 => Expr.beq a0 b0 && Expr.beq a1 b1
  | .and a0 a1, .and b0 b1 => Expr.beq a0 b0 && Expr.beq a1 b1
  | .or a0 a1, .or b0 b1 => Expr.beq a0 b0 && Expr.beq a1 b1
  | .decide a0, .decide b0 => Expr.beq a0 b0
  | .numberTest a0 a1, .numberTest b0 b1 => Decidable.decide (a0 = b0) && Expr.beq a1 b1
  | .push a0 a1, .push b0 b1 => Decidable.decide (a0 = b0) && Expr.beq a1 b1
  | .update a0 a1 a2, .update b0 b1 b2 => Decidable.decide (a0 = b0) && Decidable.decide (a1 = b1) && Expr.beq a2 b2
  | _, _ => false

def Expr.beqList : List Expr → List Expr → Bool
  | [], [] => true
  | x :: xs, y :: ys => Expr.beq x y && Expr.beqList xs ys
  | _, _ => false

def Expr.beqFields : List (String × Expr) → List (String × Expr) → Bool
  | [], [] => true
  | (k, x) :: xs, (l, y) :: ys => Decidable.decide (k = l) && Expr.beq x y && Expr.beqFields xs ys
  | _, _ => false

end

mutual

theorem Expr.beq_iff : (a b : Expr) → Expr.beq a b = true ↔ a = b
  | .int a0, b => by
    cases b <;> simp [and_assoc, Expr.beq]
  | .number a0, b => by
    cases b <;> simp [and_assoc, Expr.beq]
  | .numberConstant a0, b => by
    cases b <;> simp [and_assoc, Expr.beq]
  | .none, b => by
    cases b <;> simp [and_assoc, Expr.beq]
  | .bool a0, b => by
    cases b <;> simp [and_assoc, Expr.beq]
  | .string a0, b => by
    cases b <;> simp [and_assoc, Expr.beq]
  | .var a0, b => by
    cases b <;> simp [and_assoc, Expr.beq]
  | .field a0 a1 a2, b => by
    cases b <;> simp [and_assoc, Expr.beq, Expr.beq_iff a0]
  | .propNot a0, b => by
    cases b <;> simp [and_assoc, Expr.beq, Expr.beq_iff a0]
  | .not a0, b => by
    cases b <;> simp [and_assoc, Expr.beq, Expr.beq_iff a0]
  | .neg a0, b => by
    cases b <;> simp [and_assoc, Expr.beq, Expr.beq_iff a0]
  | .numberNeg a0, b => by
    cases b <;> simp [and_assoc, Expr.beq, Expr.beq_iff a0]
  | .ite a0 a1 a2, b => by
    cases b <;> simp [and_assoc, Expr.beq, Expr.beq_iff a0, Expr.beq_iff a1, Expr.beq_iff a2]
  | .call a0 a1, b => by
    cases b <;> simp [and_assoc, Expr.beq, Expr.beqList_iff a1]
  | .list a0 a1, b => by
    cases b <;> simp [and_assoc, Expr.beq, Expr.beqList_iff a0]
  | .struct a0 a1, b => by
    cases b <;> simp [and_assoc, Expr.beq, Expr.beqFields_iff a0]
  | .isNone a0, b => by
    cases b <;> simp [and_assoc, Expr.beq, Expr.beq_iff a0]
  | .isSome a0, b => by
    cases b <;> simp [and_assoc, Expr.beq, Expr.beq_iff a0]
  | .matchNull a0 a1 a2, b => by
    cases b <;> simp [and_assoc, Expr.beq, Expr.beq_iff a1, Expr.beq_iff a2]
  | .intOp a0 a1 a2, b => by
    cases b <;> simp [and_assoc, Expr.beq, Expr.beq_iff a1, Expr.beq_iff a2]
  | .order a0 a1 a2, b => by
    cases b <;> simp [and_assoc, Expr.beq, Expr.beq_iff a1, Expr.beq_iff a2]
  | .division a0 a1 a2, b => by
    cases b <;> simp [and_assoc, Expr.beq, Expr.beq_iff a1, Expr.beq_iff a2]
  | .numberOp a0 a1 a2, b => by
    cases b <;> simp [and_assoc, Expr.beq, Expr.beq_iff a1, Expr.beq_iff a2]
  | .numberNe a0 a1, b => by
    cases b <;> simp [and_assoc, Expr.beq, Expr.beq_iff a0, Expr.beq_iff a1]
  | .eq a0 a1, b => by
    cases b <;> simp [and_assoc, Expr.beq, Expr.beq_iff a0, Expr.beq_iff a1]
  | .ne a0 a1, b => by
    cases b <;> simp [and_assoc, Expr.beq, Expr.beq_iff a0, Expr.beq_iff a1]
  | .propAnd a0 a1, b => by
    cases b <;> simp [and_assoc, Expr.beq, Expr.beq_iff a0, Expr.beq_iff a1]
  | .propOr a0 a1, b => by
    cases b <;> simp [and_assoc, Expr.beq, Expr.beq_iff a0, Expr.beq_iff a1]
  | .and a0 a1, b => by
    cases b <;> simp [and_assoc, Expr.beq, Expr.beq_iff a0, Expr.beq_iff a1]
  | .or a0 a1, b => by
    cases b <;> simp [and_assoc, Expr.beq, Expr.beq_iff a0, Expr.beq_iff a1]
  | .decide a0, b => by
    cases b <;> simp [and_assoc, Expr.beq, Expr.beq_iff a0]
  | .numberTest a0 a1, b => by
    cases b <;> simp [and_assoc, Expr.beq, Expr.beq_iff a1]
  | .push a0 a1, b => by
    cases b <;> simp [and_assoc, Expr.beq, Expr.beq_iff a1]
  | .update a0 a1 a2, b => by
    cases b <;> simp [and_assoc, Expr.beq, Expr.beq_iff a2]

theorem Expr.beqList_iff : (xs ys : List Expr) → Expr.beqList xs ys = true ↔ xs = ys
  | [], ys => by cases ys <;> simp [and_assoc, Expr.beqList]
  | x :: xs, ys => by
    cases ys <;> simp [and_assoc, Expr.beqList, Expr.beq_iff x, Expr.beqList_iff xs]

theorem Expr.beqFields_iff : (xs ys : List (String × Expr)) → Expr.beqFields xs ys = true ↔ xs = ys
  | [], ys => by cases ys <;> simp [and_assoc, Expr.beqFields]
  | (k, x) :: xs, ys => by
    cases ys with
    | nil => simp [Expr.beqFields]
    | cons y ys =>
      obtain ⟨l, y⟩ := y
      simp [and_assoc, Expr.beqFields, Expr.beq_iff x, Expr.beqFields_iff xs]

end

instance : DecidableEq Expr := fun a b => decidable_of_iff _ (Expr.beq_iff a b)

deriving instance DecidableEq for LoopInfo, Body, Decl

end tolean.TypeScript.Output
