import GraphQL.Schema

/-! Lookup facts for opaque custom-scalar payloads. -/

namespace GraphQL.Schema

theorem lookupCustomScalar_type {schema : Schema} {name : Name}
    {scalar : CustomScalarType}
    (hlookup : schema.lookupCustomScalar name = some scalar)
    : schema.lookupType name = some (.customScalar scalar) := by
  cases htype : schema.lookupType name with
  | none => simp [lookupCustomScalar, htype] at hlookup
  | some definition =>
      cases definition <;> simp [lookupCustomScalar, htype] at hlookup
      case customScalar candidate =>
        subst candidate
        rfl

theorem lookupInputObject_eq_none_of_lookupCustomScalar {schema : Schema} {name : Name}
    {scalar : CustomScalarType}
    (hlookup : schema.lookupCustomScalar name = some scalar)
    : schema.lookupInputObject name = none := by
  simp [lookupInputObject, lookupCustomScalar_type hlookup]

end GraphQL.Schema
