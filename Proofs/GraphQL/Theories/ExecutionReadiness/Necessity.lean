import GraphQL.Theories.ExecutionReadiness
import Proofs.GraphQL.SchemaWellFormedness.FieldLookup
import Proofs.GraphQL.Validation.FieldMerge

/-! Independent counterexamples for the two semantic execution-readiness premises. -/

namespace GraphQL
namespace ExecutionReadiness.Necessity

open Execution SchemaWellFormedness

-- The interface default is deliberately absent from the concrete field.
private def requiredArgument : InputValueDefinition :=
  { name := "a", inputType := .nonNull (.named "Int") }

private def concreteField : FieldDefinition :=
  { name := "f", outputType := .named "String", arguments := [requiredArgument] }

private def declaredField : FieldDefinition :=
  {
    concreteField with
      arguments := [{ requiredArgument with defaultValue := some (.int 1) }]
  }

private def deadField : FieldDefinition :=
  { name := "dead", outputType := .nonNull (.named "Empty") }

private def interfaceType : InterfaceType := { name := "I", fields := [declaredField] }

-- No object implements this interface. A singular non-null return cannot be completed.
private def emptyType : InterfaceType :=
  { name := "Empty", fields := [{ name := "name", outputType := .named "String" }] }

private def rootType : ObjectType :=
  { name := "Query", interfaces := ["I"], fields := [concreteField, deadField] }

private def schema : Schema :=
  {
    queryType := "Query",
    types := [.interface interfaceType, .interface emptyType, .object rootType]
  }

attribute [local simp] schema requiredArgument concreteField declaredField deadField
  interfaceType emptyType rootType Schema.lookupType Schema.allTypes
  Schema.builtinScalarDefinitions TypeDefinition.name TypeDefinition.fields?
  BuiltinScalar.name List.find?_cons Operation.rootType OperationType.rootType

private theorem possibleTypes (parent : Name)
    : schema.getPossibleTypes parent
      = if parent = "I" then
          ["Query"]
        else if parent = "Query" then
          ["Query"]
        else
          [] := by
  by_cases hI : parent = "I"
  · subst parent; rfl
  by_cases hQ : parent = "Query"
  · subst parent; rfl
  by_cases hInt : parent = "Int"
  · subst parent; rfl
  by_cases hFloat : parent = "Float"
  · subst parent; rfl
  by_cases hString : parent = "String"
  · subst parent; rfl
  by_cases hBoolean : parent = "Boolean"
  · subst parent; rfl
  by_cases hID : parent = "ID"
  · subst parent; rfl
  by_cases hEmpty : parent = "Empty"
  · subst parent; rfl
  simp [Schema.getPossibleTypes, beq_iff_eq, hI, hQ, Ne.symm hI, Ne.symm hQ,
    Ne.symm hInt, Ne.symm hFloat, Ne.symm hString, Ne.symm hBoolean, Ne.symm hID,
    Ne.symm hEmpty]

private theorem integerDefault_valid
    : (ConstInputValue.int 1).isCorrectType schema (.nonNull (.named "Int")) := by
  have hinput : (TypeRef.named "Int").isInputType schema :=
    ⟨.builtinScalar .int, rfl, trivial⟩
  exact .nonNull _ _ hinput
    (by simp)
    (.namedNonInputObject _ _ hinput
      (by intro fields; simp)
      (by simp)
      rfl)

private theorem stringShape
    : FieldMerge.sameTypeShape schema (.named "String") (.named "String") :=
  ⟨
    ⟨.builtinScalar .string, rfl, trivial⟩,
    ⟨.builtinScalar .string, rfl, trivial⟩,
    fun _ => rfl
  ⟩

private theorem concreteField_implements
    : fieldDefinitionImplements schema concreteField declaredField := by
  simp [fieldDefinitionImplements, Schema.outputTypeSubtype, Schema.namedOutputTypeSubtype, Schema.isSubType,
    Schema.isOutputType, TypeDefinition.isOutputType,
    argumentDefinitionsImplement, Schema.lookupArgumentDefinition]

private theorem schema_valid : schemaWellFormed schema := by
  have htypes : ∀ definition ∈ schema.types, typeDefinitionWellFormed schema definition := by
    intro definition hmem
    simp only [schema, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl <;>
      simp [typeDefinitionWellFormed, interfaceTypeWellFormed, objectTypeWellFormed,
        fieldDefinitionsWellFormed, fieldDefinitionWellFormed, inputValueDefinitionsWellFormed,
        inputValueDefinitionWellFormed, listNonempty, namesAreUnique, TypeRef.isOutputType,
        TypeRef.isInputType, Schema.isOutputType, Schema.isInputType,
        TypeDefinition.isOutputType, TypeDefinition.isInputType, fieldsImplementInterface,
        interfacesIncludeInherited, Schema.lookupInterface, Schema.lookupFieldDefinition]
    · exact integerDefault_valid
    · exact concreteField_implements
  refine ⟨by simp [namesAreUnique], ⟨rootType, rfl⟩, htypes, ⟨rfl, rfl⟩, ?_, ?_, ?_⟩
  · intro parent object hpossible
    rw [possibleTypes] at hpossible
    split at hpossible
    · have heq : object = "Query" := by simpa using hpossible
      subst object
      exact ⟨rootType, rfl⟩
    · split at hpossible
      · have heq : object = "Query" := by simpa using hpossible
        subst object
        exact ⟨rootType, rfl⟩
      · cases hpossible
  · intro parent
    rw [possibleTypes]
    split <;> (try split) <;> simp
  · intro parent object field expected hpossible hlookup
    rw [possibleTypes] at hpossible
    by_cases hmeta : field = "__typename"
    · subst field
      have heq : object = "Query" := by
        split at hpossible
        · simpa using hpossible
        · split at hpossible
          · simpa using hpossible
          · simp at hpossible
      subst object
      exact lookupField_typename_implements hlookup ⟨rootType, rfl⟩
    have hlookup : schema.lookupDeclaredField parent field = some expected := by
      simpa [Schema.lookupField, hmeta] using hlookup
    by_cases hI : parent = "I"
    · subst parent
      have heq : object = "Query" := by simpa using hpossible
      subst object
      have hfield : "f" = field ∧ declaredField = expected := by
        by_cases hf : field = "f"
        · subst field
          simpa [Schema.lookupDeclaredField] using hlookup
        · simp [Schema.lookupDeclaredField, Ne.symm hf] at hlookup
      rcases hfield with ⟨rfl, rfl⟩
      exact ⟨concreteField, rfl, concreteField_implements⟩
    by_cases hQ : parent = "Query"
    · subst parent
      have heq : object = "Query" := by simpa [hI] using hpossible
      subst object
      by_cases hf : field = "f"
      · subst field
        have heq : concreteField = expected := by simpa [Schema.lookupDeclaredField] using hlookup
        subst expected
        refine ⟨concreteField, rfl, ?_⟩
        simp [fieldDefinitionImplements, Schema.outputTypeSubtype, Schema.namedOutputTypeSubtype, Schema.isSubType,
          Schema.isOutputType, TypeDefinition.isOutputType,
          argumentDefinitionsImplement, Schema.lookupArgumentDefinition]
      · have hfield : "dead" = field ∧ deadField = expected := by
          by_cases hd : field = "dead"
          · subst field
            simpa [Schema.lookupDeclaredField] using hlookup
          · simp [Schema.lookupDeclaredField, Ne.symm hf, Ne.symm hd] at hlookup
        rcases hfield with ⟨rfl, rfl⟩
        refine ⟨deadField, rfl, ?_⟩
        simp [fieldDefinitionImplements, Schema.outputTypeSubtype, Schema.namedOutputTypeSubtype, Schema.isSubType,
          Schema.isOutputType, TypeDefinition.isOutputType,
          argumentDefinitionsImplement]
    · simp [hI, hQ] at hpossible

private def nameSelections : List Selection := [.field "name" "name" [] [] []]

private def deadOperation : Operation :=
  { selectionSet := [.field "dead" "dead" [] [] nameSelections] }

private def argumentOperation : Operation :=
  { selectionSet := [.inlineFragment (some "I") [] [.field "f" "f" [] [] []]] }

private def leafScope (parent name : Name) : FieldMerge.ScopedField :=
  {
    parentType := parent,
    responseName := name,
    fieldName := name,
    arguments := [],
    outputType := .named "String",
    selectionSet := []
  }

private def deadScope : FieldMerge.ScopedField :=
  {
    parentType := "Query",
    responseName := "dead",
    fieldName := "dead",
    arguments := [],
    outputType := .nonNull (.named "Empty"),
    selectionSet := nameSelections
  }

private theorem leafMerge (parent name : Name)
    : FieldMerge.fieldsForNameCanMerge schema (leafScope parent name)
        (leafScope parent name) := by
  apply FieldMerge.fieldsForNameCanMerge_self_of_children stringShape
    (by simp [leafScope, Argument.argumentsEquivalent])
  refine .intro _ _ ?_
  simp [leafScope, FieldMerge.collectFields]

private theorem nameChildrenMerge
    : FieldMerge.fieldsInSetCanMerge schema "Empty"
        (nameSelections ++ nameSelections) := by
  refine .intro _ _ ?_
  dsimp only
  intro left hleft right hright _
  have hcollect : FieldMerge.collectFields schema "Empty" (nameSelections ++ nameSelections)
      = [leafScope "Empty" "name", leafScope "Empty" "name"] := by
    simp [FieldMerge.collectFields, Schema.lookupField, Schema.lookupDeclaredField,
      nameSelections, leafScope]
  rw [hcollect] at hleft hright
  simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at hleft hright
  subst left
  subst right
  exact leafMerge _ _

private theorem deadMerge
    : FieldMerge.fieldsForNameCanMerge schema deadScope deadScope := by
  apply FieldMerge.fieldsForNameCanMerge_self_of_children
    (FieldMerge.sameTypeShape_refl schema (.nonNull (.named "Empty"))
      ⟨.interface emptyType, rfl, trivial⟩)
    (by simp [deadScope, Argument.argumentsEquivalent]) nameChildrenMerge

private theorem deadOperation_valid
    : Validation.operationDefinitionValid schema deadOperation := by
  refine ⟨
    rfl,
    ⟨.object rootType, rfl, trivial⟩,
    by simp [deadOperation, Validation.variableDefinitionsValid],
    by decide,
    ?_,
    ?_,
    by simp [deadOperation, Validation.operationVariablesUsed]
  ⟩
  · simp [deadOperation, nameSelections, Validation.selectionSetValid, Validation.selectionValid,
      Validation.directivesValid, Validation.argumentsValid, Validation.fieldSelectionSetValid,
      Schema.lookupField, Schema.lookupDeclaredField, TypeRef.namedType, TypeRef.isOutputType,
      Schema.isOutputType, Schema.isLeafType, Schema.isCompositeType, TypeDefinition.isOutputType,
      TypeDefinition.isLeafType, TypeDefinition.isCompositeType]
  · refine .intro _ _ ?_
    dsimp only
    intro left hleft right hright _
    have hcollect : FieldMerge.collectFields schema (deadOperation.rootType schema)
        deadOperation.selectionSet = [deadScope] := by
      simp [FieldMerge.collectFields, Schema.lookupField, Schema.lookupDeclaredField,
        deadOperation, deadScope]
    rw [hcollect] at hleft hright
    simp only [List.mem_singleton] at hleft hright
    subst left
    subst right
    exact deadMerge

private theorem argumentOperation_valid
    : Validation.operationDefinitionValid schema argumentOperation := by
  refine ⟨
    rfl,
    ⟨.object rootType, rfl, trivial⟩,
    by simp [argumentOperation, Validation.variableDefinitionsValid],
    by decide,
    ?_,
    ?_,
    by simp [argumentOperation, Validation.operationVariablesUsed]
  ⟩
  · simp [argumentOperation, Validation.selectionSetValid, Validation.selectionValid,
      Validation.directivesValid, Validation.argumentsValid, Validation.fieldSelectionSetValid,
      Validation.isRequiredArgument, Validation.isRequiredInputValueDefinition,
      InputValueDefinition.isRequired,
      Schema.lookupField, Schema.lookupDeclaredField, TypeRef.namedType, TypeRef.isOutputType,
      Schema.isOutputType, Schema.isLeafType, Schema.isCompositeType, TypeDefinition.isOutputType,
      TypeDefinition.isLeafType, TypeDefinition.isCompositeType, Schema.typesOverlap]
    exact ⟨"Query", by change "Query" ∈ ["Query"]; simp,
      by change "Query" ∈ ["Query"]; simp⟩
  · refine .intro _ _ ?_
    dsimp only
    intro left hleft right hright _
    have hcollect : FieldMerge.collectFields schema (argumentOperation.rootType schema)
        argumentOperation.selectionSet = [leafScope "I" "f"] := by
      simp [FieldMerge.collectFields, Schema.lookupField, Schema.lookupDeclaredField,
        argumentOperation, leafScope]
    rw [hcollect] at hleft hright
    simp only [List.mem_singleton] at hleft hright
    subst left
    subst right
    exact leafMerge _ _

private theorem deadOperation_coercible
    : operationCoercibleInPossibleTypes schema deadOperation := by
  intro values
  simp [selectionSetCoercibleInPossibleTypes,
    selectionCoercibleInPossibleTypes, deadOperation, selectionDirectivesAllowBool,
    Schema.lookupField, Schema.lookupDeclaredField, omittedNonNullArgumentsHaveDefaults,
    TypeRef.namedType]
  intro object hobject
  change object ∈ ([] : List Name) at hobject
  cases hobject

private theorem deadOperation_uninhabited
    : ¬ operationCompositeFieldTypesInhabited schema deadOperation := by
  intro h
  unfold operationCompositeFieldTypesInhabited selectionSetCompositeFieldTypesInhabited at h
  have hdead := h [] (.field "dead" "dead" [] [] nameSelections) (by simp [deadOperation])
  unfold selectionCompositeFieldTypesInhabited at hdead
  exact (hdead rfl deadField rfl rfl).1 rfl

private theorem argumentOperation_inhabited
    : operationCompositeFieldTypesInhabited schema argumentOperation := by
  intro values
  simp [selectionSetCompositeFieldTypesInhabited, selectionCompositeFieldTypesInhabited,
    argumentOperation, selectionDirectivesAllowBool, Schema.lookupField, Schema.lookupDeclaredField,
    TypeRef.isCompositeBool, TypeRef.namedType]

private theorem argumentOperation_notCoercible
    : ¬ operationCoercibleInPossibleTypes schema argumentOperation := by
  intro h
  have hfield := (h []).1 rfl rfl
  have harg := hfield.1 rfl
  exact Bool.noConfusion (harg.1 requiredArgument (by simp) rfl rfl)

attribute [local simp] executeQuery executeQueryWithFuel executeQueryFuelBound
  rootSourceAppliesBool runtimeObjectType? Schema.typeIncludesObjectBool
  Schema.getPossibleTypes Schema.objectTypesImplementingInterface Schema.objectTypes
  Schema.objectTypeImplementsInterfaceBool Schema.interfaceTypeImplementsInterfaceBool
  coerceVariableValues Operation.size Selection.size SelectionSet.size
  typeDefinitionsExecutionCompletionFuel fieldDefinitionsExecutionCompletionFuel
  typeRefExecutionCompletionFuel executeRootSelectionSet collectFields collectSelection
  mergeExecutableGroups addExecutableGroup selectionDirectivesAllowBool
  executeCollectedFields executeField coerceArgumentValues coerceArgumentValue
  coerceArgumentDefault TypeRef.isNonNull Argument.lookupValue? resolveFieldValue
  completeValue TypeRef.isCompositeBool TypeRef.namedType singleFieldResult
  nonNullCompletion handleFieldError Execution.Result.combine selectionSetResultToResponse
  Schema.lookupField Schema.lookupDeclaredField doesFragmentTypeApplyBool
  Schema.lookupInterface Schema.interfaceTypeImplementsInterfaceBoundedBool
  List.filterMap_cons List.filter_cons List.any_cons

private theorem deadOperation_errors {ObjectRef : Type} (resolvers : Resolvers ObjectRef)
    (values : VariableValues) (rootRef : ObjectRef)
    : (executeQuery schema resolvers values deadOperation
        (.object "Query" rootRef)).errors
      = 1 := by
  cases hresolve : resolvers.resolve "Query" "dead" [] (.object "Query" rootRef) with
  | none => simp [deadOperation, nameSelections, hresolve]
  | some value => cases value <;> simp [deadOperation, nameSelections, hresolve]

private theorem argumentOperation_errors {ObjectRef : Type}
    (resolvers : Resolvers ObjectRef) (values : VariableValues) (rootRef : ObjectRef)
    : (executeQuery schema resolvers values argumentOperation
        (.object "Query" rootRef)).errors
      = 1 := by
  simp [argumentOperation]

end ExecutionReadiness.Necessity

open ExecutionReadiness.Necessity in
theorem executionReadiness_needsInhabitedOutputs
    : ExecutionReadinessNeedsInhabitedOutputs := by
  refine ⟨schema, deadOperation, schema_valid, deadOperation_valid, deadOperation_coercible,
    deadOperation_uninhabited, ?_⟩
  intro ObjectRef resolvers values rootRef
  change (Execution.executeQuery schema resolvers values deadOperation
    (.object "Query" rootRef)).errors ≠ 0
  rw [deadOperation_errors]
  exact Nat.one_ne_zero

open ExecutionReadiness.Necessity in
theorem executionReadiness_needsCoercibleArguments
    : ExecutionReadinessNeedsCoercibleArguments := by
  refine ⟨schema, argumentOperation, schema_valid, argumentOperation_valid, argumentOperation_inhabited,
    argumentOperation_notCoercible, ?_⟩
  intro ObjectRef resolvers values rootRef
  change (Execution.executeQuery schema resolvers values argumentOperation
    (.object "Query" rootRef)).errors ≠ 0
  rw [argumentOperation_errors]
  exact Nat.one_ne_zero

end GraphQL
