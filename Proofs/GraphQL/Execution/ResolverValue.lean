import GraphQL.Execution

/-!
Compatibility helpers for treating optional resolver values as nullable internal
resolver values.
-/

namespace GraphQL

namespace Execution

variable {ObjectRef : Type}

-- Compatibility helper used by older data-only proof surfaces: a resolver error is
-- projected as a null value. The response-producing executor uses `handleFieldError`.
def resolvedValueOrNull : Option (ResolverValue ObjectRef) -> ResolverValue ObjectRef
  | none => .null
  | some value => value

@[simp]
theorem resolvedValueOrNull_none
    : resolvedValueOrNull (ObjectRef := ObjectRef) none = .null := by
  rfl

@[simp]
theorem resolvedValueOrNull_some (value : ResolverValue ObjectRef)
    : resolvedValueOrNull (some value) = value := by
  rfl

@[simp]
theorem resolvedValueOrNull_option_null
    : resolvedValueOrNull (ObjectRef := ObjectRef) Option.null = .null := by
  rfl

@[simp]
theorem resolvedValueOrNull_option_scalar (value : String)
    : resolvedValueOrNull (Option.scalar (ObjectRef := ObjectRef) value)
      = .scalar value := by
  rfl

@[simp]
theorem resolvedValueOrNull_option_object (typeName : Name) (ref : ObjectRef)
    : resolvedValueOrNull (Option.object typeName ref) = .object typeName ref := by
  rfl

@[simp]
theorem resolvedValueOrNull_option_list (values : List (ResolverValue ObjectRef))
    : resolvedValueOrNull (Option.list values) = .list values := by
  rfl

instance instCoeOptionValueToValue {ObjectRef : Type}
    : Coe (Option (ResolverValue ObjectRef)) (ResolverValue ObjectRef) where
  coe := resolvedValueOrNull

end Execution

end GraphQL
