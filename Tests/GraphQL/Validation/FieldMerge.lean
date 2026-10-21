import Proofs.GraphQL.Validation.FieldMerge

namespace GraphQL.Tests.Validation.FieldMerge

open GraphQL.FieldMerge

def returnScopeSchema : Schema :=
  {
    queryType := "Query"
    types :=
      [
        .object
          {
            name := "Query", fields := [{ name := "user", outputType := .named "User" }]
          },
        .object
          {
            name := "User", fields := [{ name := "name", outputType := .named "String" }]
          },
        .object
          { name := "Other", fields := [{ name := "name", outputType := .named "Int" }] }
      ]
  }

def directName : List Selection := [.field "name" "name" [] [] []]

def fragmentName : List Selection := [.inlineFragment (some "User") [] directName]

def returnScopeQuery : Operation :=
  {
    selectionSet :=
      [.field "user" "user" [] [] directName, .field "user" "user" [] [] fragmentName]
  }

private def userField (children : List Selection) : ScopedField :=
  {
    parentType := "Query",
    responseName := "user",
    fieldName := "user",
    arguments := [],
    outputType := .named "User",
    selectionSet := children
  }

private def nameField : ScopedField :=
  {
    parentType := "User",
    responseName := "name",
    fieldName := "name",
    arguments := [],
    outputType := .named "String",
    selectionSet := []
  }

private theorem nameField_merge
    : fieldsForNameCanMerge returnScopeSchema nameField nameField := by
  refine .intro _ _ ?_ ?_ ?_
  · refine .intro _ _ ?_ ?_
    · exact ⟨⟨.builtinScalar .string, rfl, trivial⟩,
        ⟨.builtinScalar .string, rfl, trivial⟩, fun _ => rfl⟩
    · intro _ _ subLeft hleft
      simp [collectSubfields, nameField, collectFields] at hleft
  · intro _
    exact ⟨rfl, by simp [nameField, Argument.argumentsEquivalent]⟩
  · intro _ subLeft hleft
    simp [collectSubfields, nameField, collectFields] at hleft

private theorem userField_children (left right : List Selection)
    (hleft : left = directName ∨ left = fragmentName)
    (hright : right = directName ∨ right = fragmentName)
    : collectSubfields returnScopeSchema (userField left) (userField right)
      = [nameField, nameField] := by
  rcases hleft with rfl | rfl <;> rcases hright with rfl | rfl <;>
    simp [collectSubfields, collectFields, returnScopeSchema, userField,
      directName, fragmentName, nameField, TypeRef.namedType,
      Schema.lookupField, Schema.lookupType, Schema.allTypes, Schema.builtinScalarDefinitions,
      TypeDefinition.name, TypeDefinition.fields?, BuiltinScalar.name]

private theorem userField_merge (left right : List Selection)
    (hleft : left = directName ∨ left = fragmentName)
    (hright : right = directName ∨ right = fragmentName)
    : fieldsForNameCanMerge returnScopeSchema (userField left) (userField right) := by
  have hchildren := userField_children left right hleft hright
  have hpairs : ∀ subLeft, subLeft ∈ collectSubfields returnScopeSchema
        (userField left) (userField right) ->
      ∀ subRight, subRight ∈ collectSubfields returnScopeSchema
        (userField left) (userField right) ->
      subLeft.responseName = subRight.responseName ->
      fieldsForNameCanMerge returnScopeSchema subLeft subRight := by
    intro subLeft hsubLeft subRight hsubRight _
    simp [hchildren] at hsubLeft hsubRight
    subst subLeft
    subst subRight
    exact nameField_merge
  refine .intro _ _ ?_ ?_ (fun _ => hpairs)
  · refine .intro _ _ ?_ ?_
    · exact ⟨⟨.object { name := "User", fields := [{ name := "name", outputType := .named "String" }] },
          by simp [returnScopeSchema, Schema.lookupType, Schema.allTypes,
            Schema.builtinScalarDefinitions, TypeDefinition.name, BuiltinScalar.name], trivial⟩,
        ⟨.object { name := "User", fields := [{ name := "name", outputType := .named "String" }] },
          by simp [returnScopeSchema, Schema.lookupType, Schema.allTypes,
            Schema.builtinScalarDefinitions, TypeDefinition.name, BuiltinScalar.name], trivial⟩,
        fun _ => rfl⟩
    · intro _ _ subLeft hsubLeft subRight hsubRight hresponse
      exact fieldsForNameCanMerge_sameResponseShape
        (hpairs subLeft hsubLeft subRight hsubRight hresponse)
  · intro _
    exact ⟨rfl, by simp [userField, Argument.argumentsEquivalent]⟩

theorem sameResponseShape_matchingSubfields
    : sameResponseShape returnScopeSchema
        (userField directName) (userField fragmentName) :=
  fieldsForNameCanMerge_sameResponseShape (userField_merge _ _ (Or.inl rfl) (Or.inr rfl))

theorem sameResponseShape_wrappedLeaf
    : sameResponseShape returnScopeSchema
        { nameField with outputType := .nonNull (.list (.nonNull (.named "String"))) }
        {
          nameField with
            outputType := .nonNull (.list (.nonNull (.named "String")))
        } := by
  refine .intro _ _ ?_ ?_
  · exact SchemaWellFormedness.sameTypeShape_refl returnScopeSchema _
      (by exact ⟨.builtinScalar .string, rfl, trivial⟩)
  · intro _ _ subLeft hleft
    simp [collectSubfields, nameField, collectFields] at hleft

theorem sameResponseShape_nullableMismatch_rejected
    : ¬ sameResponseShape returnScopeSchema nameField
          { nameField with outputType := .nonNull (.named "String") } := by
  intro hshape
  exact sameResponseShape_sameTypeShape hshape

theorem sameResponseShape_listMismatch_rejected
    : ¬ sameResponseShape returnScopeSchema nameField
          { nameField with outputType := .list (.named "String") } := by
  intro hshape
  exact sameResponseShape_sameTypeShape hshape

theorem sameResponseShape_nestedWrapperMismatch_rejected
    : ¬ sameResponseShape returnScopeSchema
          { nameField with outputType := .list (.named "String") }
          { nameField with outputType := .list (.nonNull (.named "String")) } := by
  intro hshape
  exact sameResponseShape_sameTypeShape hshape

/-- Field identity belongs to mergeability, not to the response-shape check. -/
theorem sameResponseShape_differentFieldNames
    : sameResponseShape returnScopeSchema nameField
        { nameField with fieldName := "nickname" } := by
  refine .intro _ _
    (fieldsForNameCanMerge_sameTypeShape (left := nameField) (right := nameField)
      nameField_merge) ?_
  intro _ _ subLeft hleft
  simp [collectSubfields, nameField, collectFields] at hleft

theorem differentFieldNames_cannotMerge
    : ¬ fieldsForNameCanMerge returnScopeSchema nameField
          { nameField with fieldName := "nickname" } := by
  intro hmerge
  have hnames := (fieldsForNameCanMerge_same_parent_identity hmerge rfl).1
  exact (by decide : ("name" : String) ≠ "nickname") hnames

/-- An unrelated object's field type must not affect the query's merged subselections. -/
theorem returnScopeQuery_canMerge
    : fieldsInSetCanMerge returnScopeSchema "Query" returnScopeQuery.selectionSet := by
  refine .intro _ _ ?_
  dsimp
  intro left hleft right hright _
  have hcollect : collectFields returnScopeSchema "Query" returnScopeQuery.selectionSet
      = [userField directName, userField fragmentName] := by
    simp [collectFields, returnScopeQuery, returnScopeSchema, userField,
      Schema.lookupField, Schema.lookupType, Schema.allTypes, Schema.builtinScalarDefinitions,
      TypeDefinition.name, TypeDefinition.fields?, BuiltinScalar.name]
  rw [hcollect] at hleft hright
  simp at hleft hright
  rcases hleft with rfl | rfl <;> rcases hright with rfl | rfl
  · exact userField_merge _ _ (Or.inl rfl) (Or.inl rfl)
  · exact userField_merge _ _ (Or.inl rfl) (Or.inr rfl)
  · exact userField_merge _ _ (Or.inr rfl) (Or.inl rfl)
  · exact userField_merge _ _ (Or.inr rfl) (Or.inr rfl)

theorem returnScopeQuery_valid
    : GraphQL.Validation.operationDefinitionValid returnScopeSchema returnScopeQuery := by
  refine ⟨rfl, ?_, ?_, by simp [returnScopeQuery], ?_, returnScopeQuery_canMerge, ?_⟩
  · exact ⟨.object { name := "Query", fields := [{ name := "user", outputType := .named "User" }] },
      by simp [returnScopeSchema, Operation.rootType, OperationType.rootType,
        Schema.lookupType, Schema.allTypes, Schema.builtinScalarDefinitions,
        TypeDefinition.name, BuiltinScalar.name], trivial⟩
  · simp [GraphQL.Validation.variableDefinitionsValid, returnScopeQuery]
  · simp [GraphQL.Validation.selectionSetValid, GraphQL.Validation.selectionValid,
      GraphQL.Validation.fieldSelectionSetValid, GraphQL.Validation.directivesValid,
      GraphQL.Validation.argumentsValid, returnScopeQuery, returnScopeSchema,
      directName, fragmentName, Operation.rootType, OperationType.rootType, TypeRef.namedType,
      TypeRef.isOutputType, Schema.isOutputType, Schema.isLeafType, Schema.isCompositeType,
      Schema.lookupField, Schema.lookupType, Schema.allTypes, Schema.builtinScalarDefinitions,
      TypeDefinition.name, TypeDefinition.fields?, TypeDefinition.isOutputType,
      TypeDefinition.isLeafType, TypeDefinition.isCompositeType, BuiltinScalar.name,
      Schema.typesOverlap, Schema.typeIncludesObject, Schema.getPossibleTypes]
  · simp [GraphQL.Validation.operationVariablesUsed, returnScopeQuery]

/-- The merged children really do conflict when reinterpreted at the unrelated type;
the successful query regression therefore depends on preserving its return scope. -/
theorem unrelatedScope_rejected
    : ¬ fieldsInSetCanMerge returnScopeSchema "Other" (directName ++ fragmentName) := by
  intro hmerge
  let otherName : ScopedField := {
    parentType := "Other", responseName := "name", fieldName := "name",
    arguments := [], outputType := .named "Int", selectionSet := []
  }
  have hcollect : collectFields returnScopeSchema "Other" (directName ++ fragmentName)
      = [otherName, nameField] := by
    simp [collectFields, directName, fragmentName, returnScopeSchema, otherName, nameField,
      Schema.lookupField, Schema.lookupType, Schema.allTypes, Schema.builtinScalarDefinitions,
      TypeDefinition.name, TypeDefinition.fields?, BuiltinScalar.name]
  have hpair := fieldsInSetCanMerge_pair (left := otherName) (right := nameField) hmerge
    (by rw [hcollect]; simp) (by rw [hcollect]; simp) rfl
  have hshape := fieldsForNameCanMerge_sameTypeShape hpair
  have hleaf : returnScopeSchema.isLeafType "Int" :=
    ⟨.builtinScalar .int, rfl, trivial⟩
  have heq : ("Int" : String) = "String" := hshape.2.2 (Or.inl hleaf)
  exact (by decide : ("Int" : String) ≠ "String") heq

def disjointReturnSchema : Schema :=
  {
    queryType := "Query"
    types :=
      [
        .object
          {
            name := "LeftBranch",
            fields := [{ name := "user", outputType := .named "User" }]
          },
        .object
          {
            name := "RightBranch",
            fields := [{ name := "user", outputType := .named "Other" }]
          }
      ]
      ++ returnScopeSchema.types
  }

private def branchField (parent returnType : Name) : ScopedField :=
  {
    parentType := parent,
    responseName := "result",
    fieldName := "user",
    arguments := [],
    outputType := .named returnType,
    selectionSet := directName
  }

/-- Composite type compatibility alone does not establish response-shape compatibility. -/
theorem sameTypeShape_differentCompositeReturns
    : SchemaWellFormedness.sameTypeShape disjointReturnSchema
        (.named "User") (.named "Other") := by
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨.object { name := "User", fields := [{ name := "name", outputType := .named "String" }] },
      by simp [disjointReturnSchema, returnScopeSchema, Schema.lookupType, Schema.allTypes,
        Schema.builtinScalarDefinitions, TypeDefinition.name, BuiltinScalar.name], trivial⟩
  · exact ⟨.object { name := "Other", fields := [{ name := "name", outputType := .named "Int" }] },
      by simp [disjointReturnSchema, returnScopeSchema, Schema.lookupType, Schema.allTypes,
        Schema.builtinScalarDefinitions, TypeDefinition.name, BuiltinScalar.name], trivial⟩
  · intro hleaf
    simp [disjointReturnSchema, returnScopeSchema, Schema.isLeafType, Schema.lookupType,
      Schema.allTypes, Schema.builtinScalarDefinitions, TypeDefinition.name,
      TypeDefinition.isLeafType, BuiltinScalar.name] at hleaf

/-- Mutually exclusive object branches still require recursively compatible shapes. -/
theorem sameResponseShape_disjointParents_nestedMismatch_rejected
    : ¬ sameResponseShape disjointReturnSchema
          (branchField "LeftBranch" "User") (branchField "RightBranch" "Other") := by
  intro hshape
  cases hshape with
  | intro _ _ _ hchildren =>
      have huser : disjointReturnSchema.isCompositeType "User" :=
        ⟨
          .object
            {
              name := "User",
              fields := [{ name := "name", outputType := .named "String" }]
            },
          by
            simp [disjointReturnSchema, returnScopeSchema, Schema.lookupType, Schema.allTypes,
              Schema.builtinScalarDefinitions, TypeDefinition.name, BuiltinScalar.name],
          trivial
        ⟩
      have hother : disjointReturnSchema.isCompositeType "Other" :=
        ⟨
          .object
            {
              name := "Other", fields := [{ name := "name", outputType := .named "Int" }]
            },
          by
            simp [disjointReturnSchema, returnScopeSchema, Schema.lookupType, Schema.allTypes,
              Schema.builtinScalarDefinitions, TypeDefinition.name, BuiltinScalar.name],
          trivial
        ⟩
      let intField : ScopedField := {
        parentType := "Other", responseName := "name", fieldName := "name",
        arguments := [], outputType := .named "Int", selectionSet := []
      }
      have hcollect : collectSubfields disjointReturnSchema
          (branchField "LeftBranch" "User") (branchField "RightBranch" "Other")
          = [nameField, intField] := by
        simp [collectSubfields, collectFields, branchField, directName, disjointReturnSchema,
          returnScopeSchema, nameField, intField, TypeRef.namedType,
          Schema.lookupField, Schema.lookupType, Schema.allTypes, Schema.builtinScalarDefinitions,
          TypeDefinition.name, TypeDefinition.fields?, BuiltinScalar.name]
      have hchild := hchildren huser hother nameField (by rw [hcollect]; simp)
        intField (by rw [hcollect]; simp) rfl
      cases hchild with
      | intro _ _ htypes _ =>
          have hleaf : disjointReturnSchema.isLeafType "String" :=
            ⟨.builtinScalar .string, rfl, trivial⟩
          have heq : ("String" : String) = "Int" := htypes.2.2 (Or.inl hleaf)
          exact (by decide : ("String" : String) ≠ "Int") heq

theorem disjointParents_nestedShapeMismatch_rejected
    : ¬ fieldsForNameCanMerge disjointReturnSchema
          (branchField "LeftBranch" "User") (branchField "RightBranch" "Other") := by
  intro hmerge
  exact sameResponseShape_disjointParents_nestedMismatch_rejected
    (fieldsForNameCanMerge_sameResponseShape hmerge)

end GraphQL.Tests.Validation.FieldMerge
