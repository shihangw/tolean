import tolean.IR

/-!
Equality on the Tolean IR, as a function that the kernel can run.

Lean cannot derive `DecidableEq` for `Expr T E` and `Ty T`, which hold lists
of themselves. So `Expr.beq` and `Ty.beq` compare two trees field by field,
and `Expr.beq_iff` and `Ty.beq_iff` prove that each is true exactly when the
trees are equal. The other types of the IR
then derive `DecidableEq`, for every language whose added types and
operations have it. A certificate uses this equality to check that the
translator gives the IR that its theorems are about: the kernel runs the
translator and compares the two.
-/
namespace tolean.IR

-- Every proof here has the same shape, so some pass a lemma that they do not use.
set_option linter.unusedSimpArgs false

deriving instance DecidableEq for IntOp, Order, Division, ListMethod

variable {T E : Type} [DecidableEq T] [DecidableEq E]

mutual

def Ty.beq : Ty T → Ty T → Bool
  | .int, .int | .bool, .bool | .string, .string => true
  | .option a, .option b => Ty.beq a b
  | .optional a, .optional b => Ty.beq a b
  | .list a, .list b => Ty.beq a b
  | .struct a, .struct b => Decidable.decide (a = b)
  | .enum a, .enum b => Decidable.decide (a = b)
  | .tagged a, .tagged b => Decidable.decide (a = b)
  | .tag a, .tag b => Decidable.decide (a = b)
  | .tuple a, .tuple b => Ty.beqList a b
  | .param a, .param b => Decidable.decide (a = b)
  | .app a as, .app b bs => Decidable.decide (a = b) && Ty.beqList as bs
  | .ext a, .ext b => Decidable.decide (a = b)
  | _, _ => false

def Ty.beqList : List (Ty T) → List (Ty T) → Bool
  | [], [] => true
  | x :: xs, y :: ys => Ty.beq x y && Ty.beqList xs ys
  | _, _ => false

end

mutual

theorem Ty.beq_iff : (a b : Ty T) → Ty.beq a b = true ↔ a = b
  | .int, b | .bool, b | .string, b | .struct _, b | .enum _, b | .tagged _, b | .tag _, b | .param _, b
  | .ext _, b => by
    cases b <;> simp [Ty.beq]
  | .option a, b | .optional a, b | .list a, b => by
    cases b <;> simp [Ty.beq, Ty.beq_iff a]
  | .tuple a, b => by
    cases b <;> simp [Ty.beq, Ty.beqList_iff a]
  | .app r a, b => by
    cases b <;> simp [Ty.beq, Ty.beqList_iff a]

theorem Ty.beqList_iff : (xs ys : List (Ty T)) → Ty.beqList xs ys = true ↔ xs = ys
  | [], ys => by cases ys <;> simp [Ty.beqList]
  | x :: xs, ys => by
    cases ys <;> simp [and_assoc, Ty.beqList, Ty.beq_iff x, Ty.beqList_iff xs]

end

instance : DecidableEq (Ty T) := fun a b => decidable_of_iff _ (Ty.beq_iff a b)

deriving instance DecidableEq for CallbackInfo

mutual

def Expr.beq : Expr T E → Expr T E → Bool
  | .int a0, .int b0 => Decidable.decide (a0 = b0)
  | .none, .none => true
  | .ascribe a0 a1, .ascribe b0 b1 => Expr.beq a0 b0 && Decidable.decide (a1 = b1)
  | .bool a0, .bool b0 => Decidable.decide (a0 = b0)
  | .string a0, .string b0 => Decidable.decide (a0 = b0)
  | .var a0, .var b0 => Decidable.decide (a0 = b0)
  | .enumCase a0 a1, .enumCase b0 b1 => Decidable.decide (a0 = b0) && Decidable.decide (a1 = b1)
  | .tagValue a0, .tagValue b0 => Decidable.decide (a0 = b0)
  | .inject a0 a1 a2, .inject b0 b1 b2 => Decidable.decide (a0 = b0) && Decidable.decide (a1 = b1) && Expr.beq a2 b2
  | .field a0 a1 a2, .field b0 b1 b2 => Expr.beq a0 b0 && Decidable.decide (a1 = b1) && Decidable.decide (a2 = b2)
  | .propNot a0, .propNot b0 => Expr.beq a0 b0
  | .not a0, .not b0 => Expr.beq a0 b0
  | .neg a0, .neg b0 => Expr.beq a0 b0
  | .ite a0 a1 a2, .ite b0 b1 b2 => Expr.beq a0 b0 && Expr.beq a1 b1 && Expr.beq a2 b2
  | .call a0 a1, .call b0 b1 => Decidable.decide (a0 = b0) && Expr.beqList a1 b1
  | .list a0 a1, .list b0 b1 => Expr.beqList a0 b0 && Decidable.decide (a1 = b1)
  | .struct a0 a1 a2, .struct b0 b1 b2 => Expr.beqFields a0 b0 && Decidable.decide (a1 = b1) && Decidable.decide (a2 = b2)
  | .isNone a0, .isNone b0 => Expr.beq a0 b0
  | .isSome a0, .isSome b0 => Expr.beq a0 b0
  | .matchNull a0 a1 a2, .matchNull b0 b1 b2 => Decidable.decide (a0 = b0) && Expr.beq a1 b1 && Expr.beq a2 b2
  | .coalesce a0 a1 a2, .coalesce b0 b1 b2 => Expr.beq a0 b0 && Expr.beq a1 b1 && Decidable.decide (a2 = b2)
  | .intOp a0 a1 a2, .intOp b0 b1 b2 => Decidable.decide (a0 = b0) && Expr.beq a1 b1 && Expr.beq a2 b2
  | .order a0 a1 a2, .order b0 b1 b2 => Decidable.decide (a0 = b0) && Expr.beq a1 b1 && Expr.beq a2 b2
  | .division a0 a1 a2, .division b0 b1 b2 => Decidable.decide (a0 = b0) && Expr.beq a1 b1 && Expr.beq a2 b2
  | .eq a0 a1, .eq b0 b1 => Expr.beq a0 b0 && Expr.beq a1 b1
  | .ne a0 a1, .ne b0 b1 => Expr.beq a0 b0 && Expr.beq a1 b1
  | .propAnd a0 a1, .propAnd b0 b1 => Expr.beq a0 b0 && Expr.beq a1 b1
  | .propOr a0 a1, .propOr b0 b1 => Expr.beq a0 b0 && Expr.beq a1 b1
  | .and a0 a1, .and b0 b1 => Expr.beq a0 b0 && Expr.beq a1 b1
  | .or a0 a1, .or b0 b1 => Expr.beq a0 b0 && Expr.beq a1 b1
  | .decide a0, .decide b0 => Expr.beq a0 b0
  | .push a0 a1, .push b0 b1 => Decidable.decide (a0 = b0) && Expr.beq a1 b1
  | .update a0 a1 a2, .update b0 b1 b2 => Decidable.decide (a0 = b0) && Decidable.decide (a1 = b1) && Expr.beq a2 b2
  | .ext a0 a1, .ext b0 b1 => Decidable.decide (a0 = b0) && Expr.beqList a1 b1
  | .tuple a0, .tuple b0 => Expr.beqList a0 b0
  | .proj a0 a1 a2, .proj b0 b1 b2 => Expr.beq a0 b0 && Decidable.decide (a1 = b1) && Decidable.decide (a2 = b2)
  | .structUpdate a0 a1, .structUpdate b0 b1 => Expr.beq a0 b0 && Expr.beqFields a1 b1
  | .listMethod a0 a1 a2 a3 a4 a5, .listMethod b0 b1 b2 b3 b4 b5 =>
    Decidable.decide (a0 = b0) && Expr.beq a1 b1 && Decidable.decide (a2 = b2) &&
      Decidable.decide (a3 = b3) && Expr.beq a4 b4 && Decidable.decide (a5 = b5)
  | _, _ => false

def Expr.beqList : List (Expr T E) → List (Expr T E) → Bool
  | [], [] => true
  | x :: xs, y :: ys => Expr.beq x y && Expr.beqList xs ys
  | _, _ => false

def Expr.beqFields : List (String × Expr T E) → List (String × Expr T E) → Bool
  | [], [] => true
  | (k, x) :: xs, (l, y) :: ys => Decidable.decide (k = l) && Expr.beq x y && Expr.beqFields xs ys
  | _, _ => false

end

mutual

theorem Expr.beq_iff : (a b : Expr T E) → Expr.beq a b = true ↔ a = b
  | .int a0, b => by
    cases b <;> simp [and_assoc, Expr.beq]
  | .none, b => by
    cases b <;> simp [and_assoc, Expr.beq]
  | .ascribe a0 a1, b => by
    cases b <;> simp [and_assoc, Expr.beq, Expr.beq_iff a0]
  | .bool a0, b => by
    cases b <;> simp [and_assoc, Expr.beq]
  | .string a0, b => by
    cases b <;> simp [and_assoc, Expr.beq]
  | .var a0, b => by
    cases b <;> simp [and_assoc, Expr.beq]
  | .enumCase a0 a1, b => by
    cases b <;> simp [and_assoc, Expr.beq]
  | .tagValue a0, b => by
    cases b <;> simp [and_assoc, Expr.beq]
  | .inject a0 a1 a2, b => by
    cases b <;> simp [and_assoc, Expr.beq, Expr.beq_iff a2]
  | .field a0 a1 a2, b => by
    cases b <;> simp [and_assoc, Expr.beq, Expr.beq_iff a0]
  | .propNot a0, b => by
    cases b <;> simp [and_assoc, Expr.beq, Expr.beq_iff a0]
  | .not a0, b => by
    cases b <;> simp [and_assoc, Expr.beq, Expr.beq_iff a0]
  | .neg a0, b => by
    cases b <;> simp [and_assoc, Expr.beq, Expr.beq_iff a0]
  | .ite a0 a1 a2, b => by
    cases b <;> simp [and_assoc, Expr.beq, Expr.beq_iff a0, Expr.beq_iff a1, Expr.beq_iff a2]
  | .call a0 a1, b => by
    cases b <;> simp [and_assoc, Expr.beq, Expr.beqList_iff a1]
  | .list a0 a1, b => by
    cases b <;> simp [and_assoc, Expr.beq, Expr.beqList_iff a0]
  | .struct a0 a1 a2, b => by
    cases b <;> simp [and_assoc, Expr.beq, Expr.beqFields_iff a0]
  | .isNone a0, b => by
    cases b <;> simp [and_assoc, Expr.beq, Expr.beq_iff a0]
  | .isSome a0, b => by
    cases b <;> simp [and_assoc, Expr.beq, Expr.beq_iff a0]
  | .matchNull a0 a1 a2, b => by
    cases b <;> simp [and_assoc, Expr.beq, Expr.beq_iff a1, Expr.beq_iff a2]
  | .coalesce a0 a1 a2, b => by
    cases b <;> simp [and_assoc, Expr.beq, Expr.beq_iff a0, Expr.beq_iff a1]
  | .intOp a0 a1 a2, b => by
    cases b <;> simp [and_assoc, Expr.beq, Expr.beq_iff a1, Expr.beq_iff a2]
  | .order a0 a1 a2, b => by
    cases b <;> simp [and_assoc, Expr.beq, Expr.beq_iff a1, Expr.beq_iff a2]
  | .division a0 a1 a2, b => by
    cases b <;> simp [and_assoc, Expr.beq, Expr.beq_iff a1, Expr.beq_iff a2]
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
  | .push a0 a1, b => by
    cases b <;> simp [and_assoc, Expr.beq, Expr.beq_iff a1]
  | .update a0 a1 a2, b => by
    cases b <;> simp [and_assoc, Expr.beq, Expr.beq_iff a2]
  | .ext a0 a1, b => by
    cases b <;> simp [and_assoc, Expr.beq, Expr.beqList_iff a1]
  | .tuple a0, b => by
    cases b <;> simp [and_assoc, Expr.beq, Expr.beqList_iff a0]
  | .proj a0 a1 a2, b => by
    cases b <;> simp [and_assoc, Expr.beq, Expr.beq_iff a0]
  | .structUpdate a0 a1, b => by
    cases b <;> simp [and_assoc, Expr.beq, Expr.beq_iff a0, Expr.beqFields_iff a1]
  | .listMethod a0 a1 a2 a3 a4 a5, b => by
    cases b <;> simp [and_assoc, Expr.beq, Expr.beq_iff a1, Expr.beq_iff a4]

theorem Expr.beqList_iff : (xs ys : List (Expr T E)) → Expr.beqList xs ys = true ↔ xs = ys
  | [], ys => by cases ys <;> simp [and_assoc, Expr.beqList]
  | x :: xs, ys => by
    cases ys <;> simp [and_assoc, Expr.beqList, Expr.beq_iff x, Expr.beqList_iff xs]

theorem Expr.beqFields_iff : (xs ys : List (String × Expr T E)) →
    Expr.beqFields xs ys = true ↔ xs = ys
  | [], ys => by cases ys <;> simp [and_assoc, Expr.beqFields]
  | (k, x) :: xs, ys => by
    cases ys with
    | nil => simp [Expr.beqFields]
    | cons y ys =>
      obtain ⟨l, y⟩ := y
      simp [and_assoc, Expr.beqFields, Expr.beq_iff x, Expr.beqFields_iff xs]

end

instance : DecidableEq (Expr T E) := fun a b => decidable_of_iff _ (Expr.beq_iff a b)

deriving instance DecidableEq for LoopInfo, Body, Decl

end tolean.IR
