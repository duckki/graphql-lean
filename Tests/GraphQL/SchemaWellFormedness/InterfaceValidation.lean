import Proofs.GraphQL.SchemaWellFormedness.InterfaceInheritance

namespace GraphQL.Tests.SchemaWellFormedness.InterfaceValidation

open GraphQL.SchemaWellFormedness

private def valueField : FieldDefinition :=
  { name := "value", outputType := .named "String" }

private def interfaceType (name : Name) (parents : List Name) : InterfaceType :=
  { name := name, fields := [valueField], interfaces := parents }

private def queryType (parents : List Name) : ObjectType :=
  { name := "Query", fields := [valueField], interfaces := parents }

private def fixture (queryParents rootParents middleParents leafParents : List Name)
    : Schema :=
  {
    queryType := "Query"
    types :=
      [
        .object (queryType queryParents),
        .interface (interfaceType "Root" rootParents),
        .interface (interfaceType "Middle" middleParents),
        .interface (interfaceType "Leaf" leafParents)
      ]
  }

private def validSchema : Schema :=
  fixture ["Leaf", "Middle", "Root"] [] ["Root"] ["Middle", "Root"]

private def diamondSchema : Schema :=
  {
    queryType := "Query"
    types :=
      [
        .object (queryType ["Bottom", "Left", "Right", "Root"]),
        .interface (interfaceType "Root" []),
        .interface (interfaceType "Left" ["Root"]),
        .interface (interfaceType "Right" ["Root"]),
        .interface (interfaceType "Bottom" ["Left", "Right", "Root"])
      ]
  }

attribute [local simp]
  fixture queryType interfaceType valueField
  Schema.lookupType Schema.allTypes Schema.builtinScalarDefinitions
  TypeDefinition.name TypeDefinition.fields? BuiltinScalar.name

private theorem validTypes
    : ∀ definition ∈ validSchema.types,
        typeDefinitionWellFormed validSchema definition := by
  intro definition hdefinition
  simp only [validSchema, fixture, List.mem_cons, List.not_mem_nil, or_false] at hdefinition
  rcases hdefinition with rfl | rfl | rfl | rfl <;>
    simp [validSchema, typeDefinitionWellFormed, objectTypeWellFormed,
      interfaceTypeWellFormed, interfacesIncludeInherited, fieldDefinitionsWellFormed,
      fieldDefinitionWellFormed, inputValueDefinitionsWellFormed, fieldsImplementInterface,
      fieldDefinitionImplements, argumentDefinitionsImplement, namesAreUnique, listNonempty,
      Schema.lookupInterface, Schema.lookupFieldDefinition, TypeRef.isOutputType,
      Schema.isOutputType, TypeDefinition.isOutputType, Schema.outputTypeSubtype,
      Schema.namedOutputTypeSubtype, Schema.isSubType]

private theorem possibleTypes (parent : Name)
    : validSchema.getPossibleTypes parent
      = if parent = "Query" ∨ parent = "Root" ∨ parent = "Middle" ∨ parent = "Leaf" then
          ["Query"]
        else
          [] := by
  by_cases hQ : parent = "Query"
  · subst parent; decide
  by_cases hR : parent = "Root"
  · subst parent; decide
  by_cases hM : parent = "Middle"
  · subst parent; decide
  by_cases hL : parent = "Leaf"
  · subst parent; decide
  simp [validSchema, Schema.getPossibleTypes, hQ, hR, hM, hL,
    beq_iff_eq, Ne.symm hQ, Ne.symm hR, Ne.symm hM, Ne.symm hL]

theorem validInheritance_accepted : schemaWellFormed validSchema := by
  refine ⟨
    by simp [validSchema, namesAreUnique],
    ⟨queryType ["Leaf", "Middle", "Root"], rfl⟩,
    validTypes,
    ⟨rfl, rfl⟩,
    ?_,
    ?_,
    ?_
  ⟩
  · intro parent object hpossible
    rw [possibleTypes] at hpossible
    split at hpossible
    · have hobject : object = "Query" := by simpa using hpossible
      subst object
      exact ⟨queryType ["Leaf", "Middle", "Root"], rfl⟩
    · cases hpossible
  · intro parent
    rw [possibleTypes]
    split <;> simp
  · intro parent object field expected hpossible hlookup
    rw [possibleTypes] at hpossible
    split at hpossible
    next hparent =>
      have hobject : object = "Query" := by simpa using hpossible
      subst object
      rcases hparent with rfl | rfl | rfl | rfl
      all_goals
        have hfield : "value" = field ∧ valueField = expected := by
          simpa [validSchema, Schema.lookupField] using hlookup
        rcases hfield with ⟨rfl, rfl⟩
        refine ⟨valueField, rfl, ?_⟩
        simp [validSchema, fieldDefinitionImplements, argumentDefinitionsImplement,
          Schema.outputTypeSubtype, Schema.namedOutputTypeSubtype, Schema.isOutputType,
          TypeDefinition.isOutputType, Schema.isSubType]
    next => cases hpossible

theorem diamondInheritance_accepted : schemaWellFormed diamondSchema := by
  have htypes : ∀ definition ∈ diamondSchema.types,
      typeDefinitionWellFormed diamondSchema definition := by
    intro definition hdefinition
    simp only [diamondSchema, List.mem_cons, List.not_mem_nil, or_false] at hdefinition
    rcases hdefinition with rfl | rfl | rfl | rfl | rfl <;>
      simp [diamondSchema, typeDefinitionWellFormed, objectTypeWellFormed,
        interfaceTypeWellFormed, interfacesIncludeInherited, fieldDefinitionsWellFormed,
        fieldDefinitionWellFormed, inputValueDefinitionsWellFormed, fieldsImplementInterface,
        fieldDefinitionImplements, argumentDefinitionsImplement, namesAreUnique, listNonempty,
        Schema.lookupInterface, Schema.lookupFieldDefinition, TypeRef.isOutputType,
        Schema.isOutputType, TypeDefinition.isOutputType, Schema.outputTypeSubtype,
        Schema.namedOutputTypeSubtype, Schema.isSubType]
  have hpossibleTypes (parent : Name) : diamondSchema.getPossibleTypes parent
      = if parent = "Query" ∨ parent = "Root" ∨ parent = "Left" ∨ parent = "Right"
          ∨ parent = "Bottom" then ["Query"] else [] := by
    by_cases hQ : parent = "Query"
    · subst parent; decide
    by_cases hR : parent = "Root"
    · subst parent; decide
    by_cases hL : parent = "Left"
    · subst parent; decide
    by_cases hRight : parent = "Right"
    · subst parent; decide
    by_cases hB : parent = "Bottom"
    · subst parent; decide
    simp [diamondSchema, Schema.getPossibleTypes, hQ, hR, hL, hRight, hB,
      beq_iff_eq, Ne.symm hQ, Ne.symm hR, Ne.symm hL, Ne.symm hRight, Ne.symm hB]
  refine ⟨
    by simp [diamondSchema, namesAreUnique],
    ⟨queryType ["Bottom", "Left", "Right", "Root"], rfl⟩,
    htypes,
    ⟨rfl, rfl⟩,
    ?_,
    ?_,
    ?_
  ⟩
  · intro parent object hpossible
    rw [hpossibleTypes] at hpossible
    split at hpossible
    · have hobject : object = "Query" := by simpa using hpossible
      subst object
      exact ⟨queryType ["Bottom", "Left", "Right", "Root"], rfl⟩
    · cases hpossible
  · intro parent
    rw [hpossibleTypes]
    split <;> simp
  · intro parent object field expected hpossible hlookup
    rw [hpossibleTypes] at hpossible
    split at hpossible
    next hparent =>
      have hobject : object = "Query" := by simpa using hpossible
      subst object
      rcases hparent with rfl | rfl | rfl | rfl | rfl
      all_goals
        have hfield : "value" = field ∧ valueField = expected := by
          simpa [diamondSchema, Schema.lookupField] using hlookup
        rcases hfield with ⟨rfl, rfl⟩
        refine ⟨valueField, rfl, ?_⟩
        simp [diamondSchema, fieldDefinitionImplements, argumentDefinitionsImplement,
          Schema.outputTypeSubtype, Schema.namedOutputTypeSubtype, Schema.isOutputType,
          TypeDefinition.isOutputType, Schema.isSubType]
    next => cases hpossible

theorem diamondInheritance_sharedAncestorOnce
    : diamondSchema.getPossibleTypes "Root" = ["Query"] := by
  decide

theorem transitiveObjectAncestor_declared
    : "Root" ∈ (queryType ["Leaf", "Middle", "Root"]).interfaces := by
  apply objectTypeWellFormed_reachableInterface_declared
    (source := "Leaf")
    (schemaWellFormed_lookupType_typeDefinitionWellFormed validInheritance_accepted
      (by rfl : validSchema.lookupType "Query" = some (.object (queryType _))))
    (by decide)
  apply (interfaceTypeImplementsInterfaceBool_iff validSchema "Leaf" "Root").mp
  decide

theorem missingObjectAncestor_rejected
    : ¬ schemaWellFormed (fixture ["Leaf", "Middle"] [] ["Root"] ["Middle", "Root"]) := by
  intro hschema
  have hobject : objectTypeWellFormed _ (queryType ["Leaf", "Middle"]) :=
    schemaWellFormed_lookupType_typeDefinitionWellFormed
      (typeName := "Query") (typeDefinition := .object (queryType ["Leaf", "Middle"]))
      hschema rfl
  have hroot := hobject.2.2.2 "Middle" (by decide)
    (interfaceType "Middle" ["Root"]) rfl (by decide : "Root" ∈ ["Root"])
  exact (by decide : ¬ "Root" ∈ (["Leaf", "Middle"] : List Name)) hroot

theorem missingObjectIntermediate_rejected
    : ¬ schemaWellFormed (fixture ["Leaf", "Root"] [] ["Root"] ["Middle", "Root"]) := by
  intro hschema
  have hobject : objectTypeWellFormed _ (queryType ["Leaf", "Root"]) :=
    schemaWellFormed_lookupType_typeDefinitionWellFormed
      (typeName := "Query") (typeDefinition := .object (queryType ["Leaf", "Root"]))
      hschema rfl
  have hmiddle := hobject.2.2.2 "Leaf" (by decide)
    (interfaceType "Leaf" ["Middle", "Root"]) rfl (by decide : "Middle" ∈ ["Middle", "Root"])
  exact (by decide : ¬ "Middle" ∈ (["Leaf", "Root"] : List Name)) hmiddle

theorem missingInterfaceAncestor_rejected
    : ¬ schemaWellFormed (fixture ["Leaf", "Middle", "Root"] [] ["Root"] ["Middle"]) := by
  intro hschema
  have hinterface : interfaceTypeWellFormed _ (interfaceType "Leaf" ["Middle"]) :=
    schemaWellFormed_lookupType_typeDefinitionWellFormed
      (typeName := "Leaf") (typeDefinition := .interface (interfaceType "Leaf" ["Middle"]))
      hschema rfl
  have hroot := hinterface.2.2.2.2 "Middle" (by decide)
    (interfaceType "Middle" ["Root"]) rfl (by decide : "Root" ∈ ["Root"])
  exact (by decide : ¬ "Root" ∈ (["Middle"] : List Name)) hroot

theorem selfImplementation_rejected : ¬ schemaWellFormed (fixture [] ["Root"] [] []) := by
  intro hschema
  exact schemaWellFormed_interface_noInheritanceCycle hschema
    (by rfl
      : (fixture [] ["Root"] [] []).lookupInterface "Root"
        = some (interfaceType "Root" ["Root"]))
    (by decide : "Root" ∈ ["Root"]) (.refl _)

theorem mutualCycle_rejected
    : ¬ schemaWellFormed (fixture [] ["Middle"] ["Root"] []) := by
  intro hschema
  apply schemaWellFormed_interface_noInheritanceCycle hschema
    (by rfl
      : (fixture [] ["Middle"] ["Root"] []).lookupInterface "Root"
        = some (interfaceType "Root" ["Middle"]))
    (by decide : "Middle" ∈ ["Middle"])
  apply (interfaceTypeImplementsInterfaceBool_iff _ "Middle" "Root").mp
  decide

theorem longerCycle_rejected
    : ¬ schemaWellFormed (fixture [] ["Middle"] ["Leaf"] ["Root"]) := by
  intro hschema
  apply schemaWellFormed_interface_noInheritanceCycle hschema
    (by rfl
      : (fixture [] ["Middle"] ["Leaf"] ["Root"]).lookupInterface "Root"
        = some (interfaceType "Root" ["Middle"]))
    (by decide : "Middle" ∈ ["Middle"])
  apply (interfaceTypeImplementsInterfaceBool_iff _ "Middle" "Root").mp
  decide

theorem missingInterface_rejected
    : ¬ schemaWellFormed (fixture ["Missing"] [] [] []) := by
  intro hschema
  have hobject : objectTypeWellFormed _ (queryType ["Missing"]) :=
    schemaWellFormed_lookupType_typeDefinitionWellFormed
      (typeName := "Query") (typeDefinition := .object (queryType ["Missing"])) hschema rfl
  rcases hobject.2.2.1 "Missing" (by decide) with ⟨implemented, hlookup, _⟩
  simp [Schema.lookupInterface] at hlookup

theorem objectAsInterface_rejected : ¬ schemaWellFormed (fixture ["Query"] [] [] []) := by
  intro hschema
  have hobject : objectTypeWellFormed _ (queryType ["Query"]) :=
    schemaWellFormed_lookupType_typeDefinitionWellFormed
      (typeName := "Query") (typeDefinition := .object (queryType ["Query"])) hschema rfl
  rcases hobject.2.2.1 "Query" (by decide) with ⟨implemented, hlookup, _⟩
  simp [Schema.lookupInterface] at hlookup

end GraphQL.Tests.SchemaWellFormedness.InterfaceValidation
