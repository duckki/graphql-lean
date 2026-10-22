import Tests.GraphQL.SchemaWellFormedness.OutputCovariance
import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.OperationSemantics
import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Validity.Operation

namespace GraphQL.Tests.NormalForm.OutputCovariance

open GraphQL.NormalForm
open GraphQL.Tests.SchemaWellFormedness.OutputCovariance

private def exampleSchema : Schema :=
  schema (.named "String") (.nonNull (.named "String"))

private def valueSelections : List Selection := [.field "value" "value" [] [] []]

private def operation : Operation :=
  { selectionSet := [.field "node" "node" [] [] valueSelections] }

private def valueScope (parent : Name) (output : TypeRef) : FieldMerge.ScopedField :=
  {
    parentType := parent,
    responseName := "value",
    fieldName := "value",
    arguments := [],
    outputType := output,
    selectionSet := []
  }

private def nodeScope (children : List Selection) : FieldMerge.ScopedField :=
  {
    parentType := "Query",
    responseName := "node",
    fieldName := "node",
    arguments := [],
    outputType := .named "I",
    selectionSet := children
  }

private def groundedChildren : List Selection :=
  [
    .inlineFragment (some "Query") [] valueSelections,
    .inlineFragment (some "Plain") [] valueSelections
  ]

attribute [local simp]
  exampleSchema schema valueField interfaceType queryType plainType
  Schema.lookupType Schema.allTypes Schema.builtinScalarDefinitions
  TypeDefinition.name TypeDefinition.fields? BuiltinScalar.name List.find?
  Operation.rootType OperationType.rootType

private theorem scalarShape
    : FieldMerge.sameTypeShape exampleSchema (.named "String") (.named "String") :=
  ⟨
    ⟨.builtinScalar .string, rfl, trivial⟩,
    ⟨.builtinScalar .string, rfl, trivial⟩,
    fun _ => rfl
  ⟩

private theorem valueMerge
    : FieldMerge.fieldsForNameCanMerge exampleSchema
        (valueScope "I" (.named "String")) (valueScope "I" (.named "String")) := by
  apply FieldMerge.fieldsForNameCanMerge_self_of_children
    (field := valueScope "I" (.named "String")) scalarShape
    (by simp [valueScope, Argument.argumentsEquivalent])
  refine .intro _ _ ?_
  dsimp only
  intro left hleft
  simp [FieldMerge.collectFields, valueScope] at hleft

private theorem valueChildrenMerge
    : FieldMerge.fieldsInSetCanMerge exampleSchema "I"
        (valueSelections ++ valueSelections) := by
  refine .intro _ _ ?_
  dsimp only
  intro left hleft right hright _
  have hcollect : FieldMerge.collectFields exampleSchema "I"
      (valueSelections ++ valueSelections)
    = [valueScope "I" (.named "String"), valueScope "I" (.named "String")] := by
      simp [FieldMerge.collectFields, Schema.lookupField, valueSelections, valueScope]
  rw [hcollect] at hleft hright
  simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at hleft hright
  subst left
  subst right
  exact valueMerge

private theorem nodeMerge
    : FieldMerge.fieldsForNameCanMerge exampleSchema
        (nodeScope valueSelections) (nodeScope valueSelections) := by
  apply FieldMerge.fieldsForNameCanMerge_self_of_children
    (field := nodeScope valueSelections)
    (FieldMerge.sameTypeShape_refl exampleSchema _
      ⟨.interface (interfaceType (.named "String")), rfl, trivial⟩)
    (by simp [nodeScope, Argument.argumentsEquivalent]) valueChildrenMerge

theorem sourceOperation_valid
    : Validation.operationDefinitionValid exampleSchema operation := by
  refine ⟨
    rfl,
    ⟨.object (queryType (.nonNull (.named "String"))), rfl, trivial⟩,
    by simp [operation, Validation.variableDefinitionsValid],
    by decide,
    ?_,
    ?_,
    by simp [operation, Validation.operationVariablesUsed]
  ⟩
  · simp [operation, valueSelections, Validation.selectionSetValid, Validation.selectionValid,
      Validation.directivesValid, Validation.argumentsValid, Validation.fieldSelectionSetValid,
      Schema.lookupField, TypeRef.namedType, TypeRef.isOutputType, Schema.isOutputType,
      Schema.isLeafType, Schema.isCompositeType, TypeDefinition.isOutputType,
      TypeDefinition.isLeafType, TypeDefinition.isCompositeType]
  · refine .intro _ _ ?_
    dsimp only
    intro left hleft right hright _
    have hcollect : FieldMerge.collectFields exampleSchema
        (operation.rootType exampleSchema) operation.selectionSet
      = [nodeScope valueSelections] := by
        simp [operation, FieldMerge.collectFields, Schema.lookupField, nodeScope]
    rw [hcollect] at hleft hright
    simp only [List.mem_singleton] at hleft hright
    subst left
    subst right
    exact nodeMerge

theorem normalizationSnapshot
    : (normalizeOperation exampleSchema operation).selectionSet
      = [.field "node" "node" [] [] groundedChildren] := by
  simp [normalizeOperation, normalizeSelectionSet, normalizedField, operation,
    valueSelections, groundedChildren, objectTypeNameBool, Schema.lookupField,
    Schema.getPossibleTypes, Schema.objectTypesImplementingInterface, Schema.objectTypes,
    Schema.objectTypeImplementsInterfaceBool, Schema.interfaceTypeImplementsInterfaceBool,
    Schema.interfaceTypeImplementsInterfaceBoundedBool, Schema.lookupInterface, TypeRef.namedType,
    withoutFieldSelectionsWithResponseName, mergeSelectionSets,
    fieldSelectionsWithResponseNameInScope]

theorem sourceOperation_fieldsValidInPossibleTypes
    : operationFieldsValidInPossibleTypes exampleSchema operation := by
  simp [operationFieldsValidInPossibleTypes, Validation.selectionSetValidInPossibleTypes,
    Validation.selectionValidInPossibleTypes, operation, valueSelections,
    Validation.selectionSetValid, Validation.selectionValid, Validation.directivesValid,
    Validation.argumentsValid, Validation.fieldSelectionSetValid, Schema.lookupField,
    TypeRef.namedType, TypeRef.isOutputType, Schema.isOutputType, Schema.isLeafType,
    Schema.isCompositeType, TypeDefinition.isOutputType, TypeDefinition.isLeafType,
    TypeDefinition.isCompositeType, Schema.getPossibleTypes,
    Schema.objectTypesImplementingInterface, Schema.objectTypes,
    Schema.objectTypeImplementsInterfaceBool, Schema.interfaceTypeImplementsInterfaceBool,
    Schema.interfaceTypeImplementsInterfaceBoundedBool, Schema.lookupInterface]

theorem sourceOperation_typeConditionFeasible
    : operationTypeConditionFeasible exampleSchema operation := by
  simp [operationTypeConditionFeasible, selectionSetTypeConditionFeasible,
    selectionTypeConditionFeasible, typeConditionStackFeasible, operation, valueSelections,
    Schema.lookupField, TypeRef.namedType, Schema.getPossibleTypes,
    Schema.objectTypesImplementingInterface, Schema.objectTypes,
    Schema.objectTypeImplementsInterfaceBool, Schema.interfaceTypeImplementsInterfaceBool,
    Schema.interfaceTypeImplementsInterfaceBoundedBool, Schema.lookupInterface]

/-- Spec covariance does not imply validity of concrete normal-form branches. -/
theorem groundedOperation_invalid
    : ¬ Validation.operationDefinitionValid exampleSchema
          (normalizeOperation exampleSchema operation) := by
  intro hvalid
  have hmerge := Validation.operationDefinitionValid_fieldsInSetCanMerge hvalid
  have hroot : FieldMerge.fieldsForNameCanMerge exampleSchema
      (nodeScope groundedChildren) (nodeScope groundedChildren) := by
    apply FieldMerge.fieldsInSetCanMerge_pair hmerge
    · rw [normalizationSnapshot]
      simp [FieldMerge.collectFields, Schema.lookupField, nodeScope]
    · rw [normalizationSnapshot]
      simp [FieldMerge.collectFields, Schema.lookupField, nodeScope]
    · rfl
  have hchildren : FieldMerge.collectSubfields exampleSchema
      (nodeScope groundedChildren) (nodeScope groundedChildren)
    = [valueScope "Query" (.nonNull (.named "String")), valueScope "Plain" (.named "String"),
        valueScope "Query" (.nonNull (.named "String")), valueScope "Plain" (.named "String")]
      := by
        simp [FieldMerge.collectSubfields, FieldMerge.collectFields, Schema.lookupField,
          nodeScope, valueScope, groundedChildren, valueSelections, TypeRef.namedType]
  have hpair := FieldMerge.fieldsForNameCanMerge_collected_subfields hroot (Or.inl rfl)
    (valueScope "Query" (.nonNull (.named "String"))) (by rw [hchildren]; simp)
    (valueScope "Plain" (.named "String")) (by rw [hchildren]; simp) rfl
  exact FieldMerge.fieldsForNameCanMerge_sameTypeShape hpair

theorem sourceOperation_fieldsNotSameOutputShape
    : ¬ operationFieldsSameOutputShape exampleSchema operation := by
  intro hshapes
  have hvalue : fieldSameOutputShape exampleSchema "value" := hshapes.1.2.1.1
  exact hvalue "I" "Query" (valueField (.named "String"))
    (valueField (.nonNull (.named "String"))) (by decide) rfl rfl

/-- Semantics preservation accepts this schema without the normalization-validity premise. -/
theorem sourceOperation_semanticsPreserved
    : operationsEquivalent exampleSchema operation
        (normalizeOperation exampleSchema operation) :=
  GroundTypeNormalization.groundTypeNormalFormSemanticsPreservation exampleSchema
    operation nonNullStrengthening_accepted sourceOperation_valid
    (by simp [operationDirectiveFree, selectionSetDirectiveFree, selectionDirectiveFree,
      operation, valueSelections])

theorem unrelatedOperation_fieldsSameOutputShape
    : operationFieldsSameOutputShape exampleSchema
        { selectionSet := [.field "safe" "safe" [] [] []] } := by
  refine ⟨⟨?_, trivial⟩, trivial⟩
  intro parent object expected implementation hpossible hlookup himplementation
  have hpossible' : object ∈
      (if parent = "I" then ["Query", "Plain"] else if parent = "Query" then ["Query"]
        else if parent = "Plain" then ["Plain"] else []) := by
    simpa only [exampleSchema, possibleTypes] using hpossible
  by_cases hQ : parent = "Query"
  · subst parent
    have hobject : object = "Query" := by simpa [Schema.getPossibleTypes] using hpossible
    subst object
    have heq : expected = implementation := Option.some.inj (hlookup.symm.trans himplementation)
    subst implementation
    exact FieldMerge.sameTypeShape_refl exampleSchema _
      (SchemaWellFormedness.schemaWellFormed_lookupField_outputType
        nonNullStrengthening_accepted hlookup)
  · by_cases hI : parent = "I"
    · subst parent
      simp [Schema.lookupField] at hlookup
    by_cases hP : parent = "Plain"
    · subst parent
      simp [Schema.lookupField] at hlookup
    simp [hI, hQ, hP] at hpossible'

end GraphQL.Tests.NormalForm.OutputCovariance
