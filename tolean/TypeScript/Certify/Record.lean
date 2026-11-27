import tolean.TypeScript.IR

namespace tolean.TypeScript.Certify

/-- Ownership evidence names both the dictionary and the key variable.
The analysis forgets evidence across bindings and at callback entry. The generated
link proof still checks every lookup; this analysis only chooses its statement. -/
abbrev RecordOwners := List (String × String)

def dynamicRecordOp : IR.ExprExt → Bool
  | .recordGet ref _ | .recordGetFlatten ref _ | .optRecordGet ref _ _
  | .optRecordGetFlatten ref _ _ => ref == IR.dictionaryRef
  | _ => false

def ownRecordGuard : IR.Expr → RecordOwners
  | .ext .recordHasOwn [.var record, .var key] => [(record, key)]
  | _ => []

def recordBodyGuards : IR.Body → RecordOwners
  | .handle attempt handler => recordBodyGuards attempt ++ recordBodyGuards handler
  | .ite condition yes no =>
    ownRecordGuard condition ++ recordBodyGuards yes ++ recordBodyGuards no
  | .let _ _ rest | .letArray _ _ _ rest | .letTuple _ _ rest
  | .letLifted _ _ rest | .bind _ _ _ rest | .letBorrow _ _ _ _ _ rest =>
    recordBodyGuards rest
  | .matchNull _ _ yes no | .matchTag _ _ _ _ _ yes no =>
    recordBodyGuards yes ++ recordBodyGuards no
  | .letState _ branch rest => recordBodyGuards branch ++ recordBodyGuards rest
  | .fold _ _ body _ rest _ => recordBodyGuards body ++ recordBodyGuards rest
  | .letCall _ _ _ _ _ _ _ body _ rest => recordBodyGuards body ++ recordBodyGuards rest
  | .value _ | .state _ | .yield _ _ | .done _ _ | .exit _ _ | .throw _ => []

mutual

def unguardedRecordExpr (owners : RecordOwners) : IR.Expr → Bool
  | .ext op args =>
    let owned := match args with
      | [.var record, .var key] => owners.contains (record, key)
      | _ => false
    (dynamicRecordOp op && !owned) || unguardedRecordExprs owners args
  | .ite condition yes no =>
    unguardedRecordExpr owners condition ||
      unguardedRecordExpr (ownRecordGuard condition ++ owners) yes ||
      unguardedRecordExpr owners no
  | .coalesce value fallback _ | .eq value fallback | .ne value fallback =>
    unguardedRecordExpr owners value || unguardedRecordExpr owners fallback
  | .not value | .propNot value | .decide value | .isNone value | .isSome value =>
    unguardedRecordExpr owners value
  | .listMethod _ items _ _ body _ =>
    unguardedRecordExpr owners items || unguardedRecordExpr [] body
  | expr => expr.anyOp dynamicRecordOp

def unguardedRecordExprs (owners : RecordOwners) : List IR.Expr → Bool
  | [] => false
  | head :: tail => unguardedRecordExpr owners head || unguardedRecordExprs owners tail

end

def unguardedRecordBody (owners : RecordOwners := []) : IR.Body → Bool
  | .value value | .exit value _ | .throw value => unguardedRecordExpr owners value
  | .ite condition yes no =>
    unguardedRecordExpr owners condition ||
      unguardedRecordBody (ownRecordGuard condition ++ owners) yes ||
      unguardedRecordBody owners no
  | .let _ value rest | .letTuple _ value rest =>
    unguardedRecordExpr owners value || unguardedRecordBody [] rest
  | .letState _ branch rest =>
    unguardedRecordBody owners branch || unguardedRecordBody [] rest
  | .fold _ _ body items rest _ =>
    unguardedRecordExpr owners items ||
      unguardedRecordBody [] body || unguardedRecordBody [] rest
  | body => body.anyOp dynamicRecordOp

end tolean.TypeScript.Certify
