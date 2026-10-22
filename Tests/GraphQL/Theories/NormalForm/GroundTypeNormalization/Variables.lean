import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Validity.Variables

namespace GraphQL.Tests.NormalForm.GroundVariables

open GraphQL.NormalForm

private def nameDefinition : FieldDefinition :=
  {
    name := "name",
    outputType := .named "String",
    arguments := [{ name := "prefix", inputType := .named "String" }]
  }

private def schema : Schema :=
  {
    queryType := "Query",
    types :=
      [
        .object
          {
            name := "Query", fields := [{ name := "user", outputType := .named "User" }]
          },
        .object { name := "User", fields := [nameDefinition] },
        .object
          { name := "Other", fields := [{ name := "name", outputType := .named "Int" }] }
      ]
  }

private def arguments : List Argument :=
  [{ name := "prefix", value := .variable "prefix" }]

private def direct : List Selection := [.field "name" "name" arguments [] []]
private def fragment : List Selection := [.inlineFragment (some "User") [] direct]

private def selections : List Selection :=
  [.field "user" "user" [] [] direct, .field "user" "user" [] [] fragment]

private def nameField : FieldMerge.ScopedField :=
  {
    parentType := "User",
    responseName := "name",
    fieldName := "name",
    arguments := arguments,
    outputType := .named "String",
    selectionSet := []
  }

private def userField (children : List Selection) : FieldMerge.ScopedField :=
  {
    parentType := "Query",
    responseName := "user",
    fieldName := "user",
    arguments := [],
    outputType := .named "User",
    selectionSet := children
  }

attribute [local simp] schema nameDefinition arguments direct fragment selections
  Schema.lookupField Schema.lookupType Schema.allTypes Schema.builtinScalarDefinitions
  TypeDefinition.name TypeDefinition.fields? BuiltinScalar.name TypeRef.namedType

private theorem nameField_merge
    : FieldMerge.fieldsForNameCanMerge schema nameField nameField := by
  refine .intro _ _ (.intro _ _ ?_ ?_) ?_ ?_
  · exact FieldMerge.sameTypeShape_refl schema (.named "String")
      ⟨.builtinScalar .string, rfl, trivial⟩
  · intro _ _ child hchild
    simp [FieldMerge.collectSubfields, FieldMerge.collectFields, nameField] at hchild
  · intro _
    refine ⟨rfl, ?_⟩
    constructor <;> intro argument hargument
    all_goals
      refine ⟨argument, hargument, ?_⟩
      have heq : argument = { name := "prefix", value := .variable "prefix" } := by
        simpa only [nameField, arguments, List.mem_singleton] using hargument
      subst argument
      exact ⟨rfl, rfl⟩
  · intro _ child hchild
    simp [FieldMerge.collectSubfields, FieldMerge.collectFields, nameField] at hchild

private theorem userField_merge (left right : List Selection)
    (hleft : left = direct ∨ left = fragment)
    (hright : right = direct ∨ right = fragment)
    : FieldMerge.fieldsForNameCanMerge schema (userField left) (userField right) := by
  have hcollect : FieldMerge.collectSubfields schema (userField left) (userField right)
      = [nameField, nameField] := by
    rcases hleft with rfl | rfl <;> rcases hright with rfl | rfl <;>
      simp [FieldMerge.collectSubfields, FieldMerge.collectFields, userField, nameField]
  have hpairs : ∀ childLeft, childLeft ∈ FieldMerge.collectSubfields schema
      (userField left) (userField right) ->
      ∀ childRight, childRight ∈ FieldMerge.collectSubfields schema
        (userField left) (userField right) ->
        childLeft.responseName = childRight.responseName ->
        FieldMerge.fieldsForNameCanMerge schema childLeft childRight := by
    intro childLeft hchildLeft childRight hchildRight _
    rw [hcollect] at hchildLeft hchildRight
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at hchildLeft hchildRight
    subst childLeft
    subst childRight
    exact nameField_merge
  refine .intro _ _ (.intro _ _ ?_ ?_) ?_ (fun _ => hpairs)
  · exact FieldMerge.sameTypeShape_refl schema (.named "User")
      ⟨.object { name := "User", fields := [nameDefinition] }, by simp, trivial⟩
  · intro _ _ childLeft hchildLeft childRight hchildRight hresponse
    exact FieldMerge.fieldsForNameCanMerge_sameResponseShape
      (hpairs childLeft hchildLeft childRight hchildRight hresponse)
  · intro _
    exact ⟨rfl, by simp [userField, Argument.argumentsEquivalent]⟩

private theorem canMerge : FieldMerge.fieldsInSetCanMerge schema "Query" selections := by
  have hcollect : FieldMerge.collectFields schema "Query" selections
      = [userField direct, userField fragment] := by
    simp [FieldMerge.collectFields, userField]
  refine .intro _ _ ?_
  dsimp only
  intro left hleft right hright _
  rw [hcollect] at hleft hright
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hleft hright
  rcases hleft with rfl | rfl <;> rcases hright with rfl | rfl
  · exact userField_merge _ _ (Or.inl rfl) (Or.inl rfl)
  · exact userField_merge _ _ (Or.inl rfl) (Or.inr rfl)
  · exact userField_merge _ _ (Or.inr rfl) (Or.inl rfl)
  · exact userField_merge _ _ (Or.inr rfl) (Or.inr rfl)

private theorem runtimeSource : runtimeMergeSource schema "Query" selections := by
  apply runtimeMergeSource_of_declaredLookupReady schema
    (parentType := "Query")
    ⟨
      { name := "Query", fields := [{ name := "user", outputType := .named "User" }] },
      rfl
    ⟩
    (by decide) _ canMerge
  simp [selectionSetDeclaredLookupReady, selectionDeclaredLookupReady]

theorem unrelatedScope_rejected
    : ¬ FieldMerge.fieldsInSetCanMerge schema "Other" (direct ++ fragment) := by
  intro hmerge
  let otherField : FieldMerge.ScopedField :=
    { nameField with parentType := "Other", outputType := .named "Int" }
  have hcollect : FieldMerge.collectFields schema "Other" (direct ++ fragment)
      = [otherField, nameField] := by
    simp [FieldMerge.collectFields, otherField, nameField]
  have hpair := FieldMerge.fieldsInSetCanMerge_pair (left := otherField) (right := nameField)
    hmerge (by rw [hcollect]; simp) (by rw [hcollect]; simp) rfl
  have hshape := FieldMerge.fieldsForNameCanMerge_sameTypeShape hpair
  have hleaf : schema.isLeafType "Int" := ⟨.builtinScalar .int, rfl, trivial⟩
  have heq : ("Int" : String) = "String" := hshape.2.2 (Or.inl hleaf)
  exact (by decide : ("Int" : String) ≠ "String") heq

-- An unrelated object's conflicting return type cannot affect variable retention
-- in the actual merged child scope.
theorem nestedDuplicateVariable_preserved
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    : "prefix"
      ∈ Validation.selectionSetVariables
          (normalizeSelectionSet schema "Query" selections) := by
  refine GroundTypeNormalization.normalizeSelectionSet_variables_mem schema "prefix"
    hschema "Query" selections ["Query"]
    ⟨
      { name := "Query", fields := [{ name := "user", outputType := .named "User" }] },
      rfl
    ⟩
    (by simp) ?_ ?_ runtimeSource ?_ ?_ ?_
  · simp [GroundTypeNormalization.VariableUse.objectSatisfiesTypeConditionStack,
      Schema.getPossibleTypes]
  · simp [selectionSetSemanticsReady, selectionSemanticsReady, selectionSetLookupValid,
      selectionLookupValid, Schema.typeIncludesObjectBool, Schema.getPossibleTypes,
      Schema.typesOverlapBool]
  · simp [selectionSetDirectiveFree, selectionDirectiveFree]
  · simp [selectionSetTypeConditionFeasible, selectionTypeConditionFeasible,
      typeConditionStackFeasible, Schema.getPossibleTypes]
  · simp [Validation.selectionSetVariables, Validation.selectionVariables,
      Validation.argumentsVariables, Validation.directivesVariables,
      Validation.argumentVariables, Validation.inputValueVariables]

theorem nestedDuplicateVariable_computes
    : Validation.selectionSetVariables (normalizeSelectionSet schema "Query" selections)
      = ["prefix"] := by
  simp [normalizeSelectionSet, normalizedField, objectTypeNameBool,
    fieldSelectionsWithResponseNameInScope, withoutFieldSelectionsWithResponseName,
    mergeSelectionSets, Selection.subselections, Schema.getPossibleTypes,
    Schema.typesOverlapBool, Schema.typeIncludesObjectBool,
    Validation.selectionSetVariables, Validation.selectionVariables,
    Validation.argumentsVariables, Validation.directivesVariables,
    Validation.argumentVariables, Validation.inputValueVariables]

theorem operationVariableUse_contract (schema : Schema) (operation : Operation)
    : SchemaWellFormedness.schemaWellFormed schema
      -> Validation.operationDefinitionValid schema operation
      -> operationDirectiveFree operation
      -> operationFieldsValidInPossibleTypes schema operation
      -> operationTypeConditionFeasible schema operation
      -> Validation.operationVariablesUsed (normalizeOperation schema operation) :=
  GroundTypeNormalization.normalizeOperation_variablesUsed schema operation

end GraphQL.Tests.NormalForm.GroundVariables
