/-!
Three-state field values, after reading a property or binding a parameter.
Null and Undefined are distinct ECMAScript types (§6.1.2 and §6.1.3).
This type does not record whether an object owns a property.
-/
namespace tolean.TypeScript

abbrev JSNullish (α : Type) : Type := Option (Option α)

@[match_pattern] abbrev JSNullish.undefined {α : Type} : JSNullish α := none

@[match_pattern] abbrev JSNullish.null {α : Type} : JSNullish α := some none

@[match_pattern] abbrev JSNullish.value {α : Type} (v : α) : JSNullish α :=
  some (some v)

def JSNullish.isNull {α : Type} : JSNullish α → Bool
  | .null => true
  | _ => false

def JSNullish.isNullish {α : Type} : JSNullish α → Bool
  | .undefined | .null => true
  | .value _ => false

end tolean.TypeScript
