import tolean.TypeScript.Spec.String

/-!
The model of the error that `throw new Error(message)` throws.

`new Error(message)` makes an object whose own property `message` holds the
message (ECMA-262 §20.5.1.1, the `Error` constructor). A translated function
that can throw returns `Except JSError T`, and `throw new Error(m)` becomes
`throw (JSError.mk m)`. The object also has a `stack` property in Node, but
ECMA-262 does not define it, so the model leaves it out.

Editions: every edition Tolean supports. The `Error` constructor and its
`message` property are in the first edition.
-/
namespace tolean.TypeScript

/-- An object that `new Error(message)` makes: its message. -/
structure JSError where
  message : JSString
deriving DecidableEq, Repr, Inhabited

end tolean.TypeScript
