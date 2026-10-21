import GraphQL.SchemaWellFormedness

namespace GraphQL.Tests.Schema.OutputTypeSubtype

private def expected : InterfaceType :=
  { name := "Expected", fields := [{ name := "value", outputType := .named "String" }] }

private def unrelated : InterfaceType :=
  { name := "Unrelated", fields := [{ name := "value", outputType := .named "Int" }] }

private def declared : InterfaceType :=
  { name := "Declared", fields := expected.fields, interfaces := ["Expected"] }

private def parent : InterfaceType :=
  { name := "Parent", fields := expected.fields }

private def child : InterfaceType :=
  { name := "Child", fields := expected.fields, interfaces := ["Parent"] }

private def indirect : InterfaceType :=
  { name := "Indirect", fields := expected.fields, interfaces := ["Child"] }

private def first : ObjectType :=
  { name := "First", fields := expected.fields, interfaces := ["Parent", "Peer"] }

private def second : ObjectType :=
  { name := "Second", fields := expected.fields }

private def schema : Schema :=
  {
    queryType := "First"
    types :=
      [
        .interface expected,
        .interface unrelated,
        .interface declared,
        .interface parent,
        .interface { name := "Peer", fields := expected.fields },
        .interface child,
        .interface indirect,
        .object first,
        .object second,
        .union { name := "Pair", members := ["First", "Second"] },
        .union { name := "Single", members := ["First"] },
        .enum { name := "Color", values := ["RED"] },
        .inputObject
          {
            name := "Input",
            inputFields := [{ name := "value", inputType := .named "Int" }]
          }
      ]
  }

attribute [local simp]
  Schema.namedOutputTypeSubtype Schema.isSubType Schema.isOutputType
  Schema.lookupType Schema.allTypes Schema.builtinScalarDefinitions
  TypeDefinition.name TypeDefinition.isOutputType
  BuiltinScalar.name schema expected unrelated declared parent child indirect first second

/-- Neither interface has an implementer, but that does not make them subtypes. -/
theorem emptyPossibleTypes_doNotEstablishSubtype
    : schema.getPossibleTypes "Expected" = []
      ∧ schema.getPossibleTypes "Unrelated" = []
      ∧ ¬ schema.isSubType "Unrelated" "Expected" := by
  refine ⟨rfl, rfl, ?_⟩
  simp

theorem incompatibleCovariantField_rejected
    : ¬ SchemaWellFormedness.fieldDefinitionImplements schema
          { name := "item", outputType := .named "Unrelated" }
          { name := "item", outputType := .named "Expected" } := by
  intro himplementation
  exact emptyPossibleTypes_doNotEstablishSubtype.2.2 himplementation.1.2.2

theorem declaredInterfaceWithoutImplementers_accepted
    : schema.getPossibleTypes "Declared" = []
      ∧ schema.isSubType "Declared" "Expected" := by
  refine ⟨rfl, ?_⟩
  simp

theorem identicalNonemptyPossibleTypes_doNotEstablishSubtype
    : schema.getPossibleTypes "Parent" = ["First"]
      ∧ schema.getPossibleTypes "Peer" = ["First"]
      ∧ ¬ schema.isSubType "Parent" "Peer" := by
  refine ⟨rfl, rfl, ?_⟩
  simp

theorem outputTypeIdentity_accepted
    : ∀ name ∈ ["String", "Color", "First", "Expected", "Pair"],
        schema.namedOutputTypeSubtype name name := by
  intro name hname
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hname
  rcases hname with rfl | rfl | rfl | rfl | rfl <;> simp

theorem declaredObjectInterface_accepted : schema.isSubType "First" "Parent" := by
  simp

theorem unionObjectMember_accepted
    : schema.isSubType "First" "Pair" ∧ schema.isSubType "Second" "Pair" := by
  simp

theorem unionNonmember_rejected : ¬ schema.isSubType "Second" "Single" := by
  simp

theorem unionSubset_rejected : ¬ schema.isSubType "Single" "Pair" := by
  simp

theorem interfaceToUnion_rejected : ¬ schema.isSubType "Parent" "Pair" := by
  simp

/-- Raw inheritance reachability does not replace the spec's declared relationship. -/
theorem undeclaredTransitiveInterface_rejected
    : schema.isSubType "Indirect" "Child" ∧ ¬ schema.isSubType "Indirect" "Parent" := by
  simp

theorem nonOutputIdentity_rejected
    : schema.isSubType "Input" "Input"
      ∧ ¬ schema.namedOutputTypeSubtype "Input" "Input"
      ∧ ¬ schema.namedOutputTypeSubtype "Missing" "Missing" := by
  simp

theorem covariantListAndNonNull_accepted
    : schema.outputTypeSubtype
        (.nonNull (.list (.nonNull (.named "First")))) (.list (.named "Parent")) := by
  simp [Schema.outputTypeSubtype]

theorem wrapperMismatch_rejected
    : ¬ schema.outputTypeSubtype (.named "First") (.nonNull (.named "Parent"))
      ∧ ¬ schema.outputTypeSubtype (.list (.named "First")) (.named "Parent") := by
  simp [Schema.outputTypeSubtype]

end GraphQL.Tests.Schema.OutputTypeSubtype
