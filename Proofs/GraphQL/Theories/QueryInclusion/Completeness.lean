import Proofs.GraphQL.Execution.ArgumentCoercion
import Proofs.GraphQL.Theories.QueryInclusion.ErrorFreeExecution
import Proofs.GraphQL.Theories.QueryInclusion.Soundness
import Proofs.GraphQL.Theories.QueryInclusion.GuardedFieldGroup

/-! Completeness of the executable query-inclusion checker. -/

namespace GraphQL
namespace QueryInclusion

open Execution AnnotatedExecution
open Execution.FieldGroups
open SelectionConditions
open Algorithms.ExecutionUngroupedUncached
open Algorithms.ExecutionUngroupedUncached.Eager

private theorem valid_operations_rootType_eq
    {schema : Schema} {left right : Operation}
    (hleft : Validation.operationDefinitionValid schema left)
    (hright : Validation.operationDefinitionValid schema right)
    : left.rootType schema = right.rootType schema := by
  rw [Validation.operationDefinitionValid_rootType_eq hleft,
    Validation.operationDefinitionValid_rootType_eq hright]

theorem includes_spine_responses
    {schema : Schema} {left right : Operation}
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (hleftValid : Validation.operationDefinitionValid schema left)
    (hrightValid : Validation.operationDefinitionValid schema right)
    (hleftInhabited : operationCompositeFieldTypesInhabited schema left)
    (hrightInhabited : operationCompositeFieldTypesInhabited schema right)
    (hincludes : includes schema left right)
    (plan : RuntimePlan) (hplan : plan.Valid schema)
    (suppliedValues : VariableValues)
    (hleftCoercion : operationArgumentsCoercible schema suppliedValues left)
    (hrightCoercion : operationArgumentsCoercible schema suppliedValues right)
    : ∃ leftFields rightFields,
        executeQueryAnnotated schema (spineResolvers schema) suppliedValues
            left (.object (left.rootType schema) plan)
          = { data := .object (left.rootType schema) leftFields, errors := 0 }
        ∧ executeQueryAnnotated schema (spineResolvers schema) suppliedValues
            right (.object (left.rootType schema) plan)
          = { data := .object (left.rootType schema) rightFields, errors := 0 }
        ∧ annotatedResponseValueIncludes (.object (left.rootType schema) leftFields)
            (.object (left.rootType schema) rightFields) := by
  have hroot := valid_operations_rootType_eq hleftValid hrightValid
  rcases executeQueryAnnotated_spine_supported schema plan hplan suppliedValues left
      hschema hleftValid hleftCoercion hleftInhabited with ⟨leftFields, hleft⟩
  rcases executeQueryAnnotated_spine_supported schema plan hplan suppliedValues right
      hschema hrightValid hrightCoercion hrightInhabited with ⟨rightFields, hright⟩
  rw [← hroot] at hright
  refine ⟨leftFields, rightFields, hleft, hright, ?_⟩
  have hsemantic := hincludes.2 RuntimePlan (spineResolvers schema)
    suppliedValues (.object (left.rootType schema) plan)
  dsimp only at hsemantic
  rw [hleft, hright] at hsemantic
  exact hsemantic rfl rfl

def wrapCompositeResponse : TypeRef -> AnnotatedResponseValue -> AnnotatedResponseValue
  | .named _typeName, value => value
  | .list inner, value => .list [wrapCompositeResponse inner value]
  | .nonNull inner, value => wrapCompositeResponse inner value

theorem annotatedResponseValueIncludes_wrapComposite
    (fieldType : TypeRef) (left right : AnnotatedResponseValue)
    (hincludes
      : annotatedResponseValueIncludes
          (wrapCompositeResponse fieldType left)
          (wrapCompositeResponse fieldType right))
    : annotatedResponseValueIncludes left right := by
  induction fieldType with
  | named typeName => exact hincludes
  | nonNull inner ih =>
      exact ih hincludes
  | list inner ih =>
      simp only [wrapCompositeResponse, annotatedResponseValueIncludes] at hincludes
      rcases hincludes 0 (wrapCompositeResponse inner right) (by simp) with
        ⟨leftValue, hleft, hvalue⟩
      simp at hleft
      subst leftValue
      exact ih hvalue

theorem executeAnnotatedCollectedFields_group_annotation
    (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variableValues : VariableValues) (fuel : Nat)
    (source : ResolverValue ObjectRef)
    (groups : List (Name × List ExecutableField))
    (responseFields : List AnnotatedResponseField)
    (hresult
      : executeQueryAnnotatedCollectedFields schema resolvers variableValues fuel
          source groups
        = .ok (responseFields, 0))
    {responseName : Name} {fields : List ExecutableField}
    (hgroup : (responseName, fields) ∈ groups)
    : ∃ completionFuel field rest definition resolved responseValue,
        fuel = completionFuel + 1
        ∧ fields = field :: rest
        ∧ schema.lookupField field.parentType field.fieldName = some definition
        ∧ coerceAndResolveFieldValue schema resolvers variableValues definition
            field.parentType field.fieldName field.arguments source
          = some resolved
        ∧ completeAnnotatedResponseValue schema resolvers variableValues
            completionFuel definition.outputType (field :: rest) resolved
          = .ok (responseValue, 0)
        ∧ .resolved responseName
            (resolvedFieldProvenance schema variableValues definition field) responseValue
          ∈ responseFields := by
  rcases executeAnnotatedCollectedFields_group_result schema resolvers variableValues
      fuel source groups responseFields hresult hgroup with
    ⟨groupResponseFields, hgroupResult, hmembers⟩
  rcases executeAnnotatedField_ok_zero_decompose schema resolvers variableValues fuel
      source responseName fields groupResponseFields hgroupResult with
    ⟨completionFuel, field, rest, definition, resolved, responseValue,
      hfuel, hfields, hlookup, hresolve, hcomplete, hresponse⟩
  refine ⟨completionFuel, field, rest, definition, resolved, responseValue,
    hfuel, hfields, hlookup, hresolve, hcomplete, ?_⟩
  apply hmembers
  rw [hresponse]
  simp

theorem completeSpineValue_composite_decompose
    (schema : Schema) (plan : RuntimePlan) (hplan : plan.Valid schema)
    (variableValues : VariableValues) (fuel : Nat)
    (fieldType : TypeRef) (fields : List ExecutableField)
    (responseValue : AnnotatedResponseValue)
    (hcomposite : fieldType.isCompositeBool schema = true)
    (hpossible : schema.getPossibleTypes fieldType.namedType ≠ [])
    (hresult
      : completeAnnotatedResponseValue schema
          (spineResolvers schema) variableValues fuel fieldType fields
          (spineResolverValue schema plan fieldType)
        = .ok (responseValue, 0))
    : ∃ childFuel childFields,
        executeQueryAnnotatedCollectedFields schema
            (spineResolvers schema) variableValues childFuel
            (.object (plan 0 fieldType.namedType) plan.shift)
            (collectSubfields schema variableValues (plan 0 fieldType.namedType)
              (.object (plan 0 fieldType.namedType) plan.shift) fields)
          = .ok (childFields, 0)
        ∧ responseValue
          = wrapCompositeResponse fieldType
              (.object (plan 0 fieldType.namedType) childFields) := by
  induction fieldType generalizing fuel responseValue with
  | named typeName =>
      cases fuel with
      | zero => simp [completeAnnotatedResponseValue] at hresult
      | succ childFuel =>
          have hruntime := spineRuntime_eq_of_valid schema plan hplan
            typeName hpossible
          have hincludes :
              schema.typeIncludesObjectBool typeName (plan 0 typeName) = true :=
            List.contains_iff_mem.mpr (hplan 0 typeName hpossible)
          have hcaught := catchAnnotated_eq_ok_zero_of_error_positive
            ((annotatedExecution_error_positive_all schema
              (spineResolvers schema) variableValues).1 childFuel
              (.object (plan 0 typeName) plan.shift)
              (collectSubfields schema variableValues (plan 0 typeName)
                (.object (plan 0 typeName) plan.shift) fields))
            (by simpa [completeAnnotatedResponseValue, spineResolverValue,
                hcomposite, hruntime, hincludes]
              using hresult)
          rcases hcaught with ⟨childFields, hchild, hvalue⟩
          exact ⟨childFuel, childFields, hchild, by
            simpa [wrapCompositeResponse, TypeRef.namedType] using hvalue⟩
  | list inner ih =>
      cases fuel with
      | zero => simp [completeAnnotatedResponseValue] at hresult
      | succ listFuel =>
          have hcaught := catchAnnotated_eq_ok_zero_of_error_positive
            ((annotatedExecution_error_positive_all schema
              (spineResolvers schema) variableValues).2.2.2 listFuel inner
              fields [spineResolverValue schema plan inner])
            (by simpa [completeAnnotatedResponseValue, spineResolverValue]
              using hresult)
          rcases hcaught with ⟨completedValues, hvalues, hresponse⟩
          simp only [completeAnnotatedResponseValueList] at hvalues
          change Result.combine List.cons
              (completeAnnotatedResponseValue schema
                (spineResolvers schema) variableValues listFuel inner fields
                (spineResolverValue schema plan inner))
              (.ok ([], 0)) = .ok (completedValues, 0) at hvalues
          rcases resultCombine_eq_ok_zero hvalues with
            ⟨headValue, tailValues, hhead, htail, hcons⟩
          simp only [Except.ok.injEq, Prod.mk.injEq, and_true] at htail
          subst tailValues
          have hcompletedValues : completedValues = [headValue] := by
            simpa using hcons.symm
          subst completedValues
          have hinnerComposite : inner.isCompositeBool schema = true := by
            simpa [TypeRef.isCompositeBool, TypeRef.namedType] using hcomposite
          rcases ih listFuel headValue hinnerComposite (by
              simpa [TypeRef.namedType] using hpossible) hhead with
            ⟨childFuel, childFields, hchild, hheadValue⟩
          refine ⟨childFuel, childFields, ?_, ?_⟩
          · simpa [TypeRef.namedType] using hchild
          · rw [hresponse, hheadValue]
            simp [wrapCompositeResponse, TypeRef.namedType]
  | nonNull inner ih =>
      cases fuel with
      | zero => simp [completeAnnotatedResponseValue] at hresult
      | succ innerFuel =>
          have hresult' : completeNonNullAnnotatedResponseValue
              (completeAnnotatedResponseValue schema
                (spineResolvers schema) variableValues (innerFuel + 1)
                inner fields (spineResolverValue schema plan inner))
              = .ok (responseValue, 0) := by
            simpa [completeAnnotatedResponseValue, spineResolverValue] using hresult
          have hinner := completeNonNull_eq_ok_zero hresult'
          have hinnerComposite : inner.isCompositeBool schema = true := by
            simpa [TypeRef.isCompositeBool, TypeRef.namedType] using hcomposite
          rcases ih (innerFuel + 1) responseValue hinnerComposite (by
              simpa [TypeRef.namedType] using hpossible) hinner.1 with
            ⟨childFuel, childFields, hchild, hvalue⟩
          exact ⟨childFuel, childFields, by
            simpa [TypeRef.namedType] using hchild, by
            simpa [wrapCompositeResponse, TypeRef.namedType] using hvalue⟩

theorem executeAnnotatedCollectedFields_success_unique
    (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variableValues : VariableValues) (source : ResolverValue ObjectRef)
    (groups : List (Name × List ExecutableField))
    {leftFuel rightFuel : Nat}
    {leftFields rightFields : List AnnotatedResponseField}
    (hleft
      : executeQueryAnnotatedCollectedFields schema resolvers variableValues
          leftFuel source groups
        = .ok (leftFields, 0))
    (hright
      : executeQueryAnnotatedCollectedFields schema resolvers variableValues
          rightFuel source groups
        = .ok (rightFields, 0))
    : leftFields = rightFields := by
  let commonFuel := max leftFuel rightFuel
  have hleftCommon : executeQueryAnnotatedCollectedFields schema resolvers
      variableValues commonFuel source groups = .ok (leftFields, 0) := by
    rw [show commonFuel = leftFuel + (commonFuel - leftFuel) by
      exact (Nat.add_sub_of_le (Nat.le_max_left _ _)).symm]
    exact executeQueryAnnotatedCollectedFields_success_mono schema resolvers
      variableValues leftFuel source groups leftFields hleft _
  have hrightCommon : executeQueryAnnotatedCollectedFields schema resolvers
      variableValues commonFuel source groups = .ok (rightFields, 0) := by
    rw [show commonFuel = rightFuel + (commonFuel - rightFuel) by
      exact (Nat.add_sub_of_le (Nat.le_max_right _ _)).symm]
    exact executeQueryAnnotatedCollectedFields_success_mono schema resolvers
      variableValues rightFuel source groups rightFields hright _
  have heq : (.ok (leftFields, 0) : Result (List AnnotatedResponseField))
      = .ok (rightFields, 0) := hleftCommon.symm.trans hrightCommon
  exact congrArg Prod.fst (Except.ok.inj heq)

def SpineSelectionIncludes
    (schema : Schema) (leftValues rightValues : VariableValues)
    (parentType runtimeType : Name)
    (leftSelectionSet rightSelectionSet : List Selection)
    : Prop :=
  ∀ plan,
    plan.Valid schema
    -> ∀ leftFuel rightFuel leftFields rightFields,
        executeQueryAnnotatedCollectedFields schema
            (spineResolvers schema) leftValues leftFuel
            (.object runtimeType plan)
            (collectFields schema leftValues parentType (.object runtimeType plan)
              leftSelectionSet)
          = .ok (leftFields, 0)
        -> executeQueryAnnotatedCollectedFields schema
              (spineResolvers schema) rightValues rightFuel
              (.object runtimeType plan)
              (collectFields schema rightValues parentType (.object runtimeType plan)
                rightSelectionSet)
            = .ok (rightFields, 0)
        -> annotatedResponseValueIncludes (.object runtimeType leftFields)
            (.object runtimeType rightFields)

theorem includes_root_spineSelectionIncludes
    {schema : Schema} {left right : Operation}
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (hleftValid : Validation.operationDefinitionValid schema left)
    (hrightValid : Validation.operationDefinitionValid schema right)
    (hleftInhabited : operationCompositeFieldTypesInhabited schema left)
    (hrightInhabited : operationCompositeFieldTypesInhabited schema right)
    (hincludes : includes schema left right)
    (suppliedValues : VariableValues)
    (hleftCoercion : operationArgumentsCoercible schema suppliedValues left)
    (hrightCoercion : operationArgumentsCoercible schema suppliedValues right)
    : SpineSelectionIncludes schema
        (coerceVariableValues left suppliedValues)
        (coerceVariableValues right suppliedValues)
        (left.rootType schema) (left.rootType schema)
        left.selectionSet right.selectionSet := by
  intro plan hplan leftFuel rightFuel leftFields rightFields hleft hright
  have hroot := valid_operations_rootType_eq hleftValid hrightValid
  rcases includes_spine_responses hschema hleftValid hrightValid hleftInhabited
      hrightInhabited hincludes plan hplan suppliedValues hleftCoercion
      hrightCoercion with
    ⟨operationLeftFields, operationRightFields, hleftOperation, hrightOperation,
      hoperationIncludes⟩
  have hleftErrors :
      (executeQueryAnnotated schema (spineResolvers schema) suppliedValues
        left (.object (left.rootType schema) plan)).errors = 0 := by
    rw [hleftOperation]
  rcases executeQueryAnnotated_zero_error_decompose schema
      (spineResolvers schema) suppliedValues left
      (.object (left.rootType schema) plan) hleftErrors with
    ⟨leftRuntime, leftPlan, collectedLeftFields, hleftSource, _hleftRuntime,
      hleftData, hleftCollected⟩
  injection hleftSource with hleftRuntimeEq hleftPlanEq
  subst leftRuntime
  subst leftPlan
  rw [hleftOperation] at hleftData
  injection hleftData with hoperationLeftFieldsEq
  subst operationLeftFields
  have hleftFieldsEq : leftFields = collectedLeftFields :=
    executeAnnotatedCollectedFields_success_unique schema
      (spineResolvers schema) (coerceVariableValues left suppliedValues)
      (.object (left.rootType schema) plan)
      (collectFields schema (coerceVariableValues left suppliedValues)
        (left.rootType schema) (.object (left.rootType schema) plan)
        left.selectionSet) hleft hleftCollected
  have hrightErrors :
      (executeQueryAnnotated schema (spineResolvers schema) suppliedValues
        right (.object (left.rootType schema) plan)).errors = 0 := by
    rw [hrightOperation]
  rcases executeQueryAnnotated_zero_error_decompose schema
      (spineResolvers schema) suppliedValues right
      (.object (left.rootType schema) plan) hrightErrors with
    ⟨rightRuntime, rightPlan, collectedRightFields, hrightSource, _hrightRuntime,
      hrightData, hrightCollected⟩
  injection hrightSource with hrightRuntimeEq hrightPlanEq
  subst rightRuntime
  subst rightPlan
  rw [hrightOperation] at hrightData
  injection hrightData with hoperationRightFieldsEq
  subst operationRightFields
  have hright' : executeQueryAnnotatedCollectedFields schema
      (spineResolvers schema) (coerceVariableValues right suppliedValues)
      rightFuel (.object (left.rootType schema) plan)
      (collectFields schema (coerceVariableValues right suppliedValues)
        (right.rootType schema) (.object (left.rootType schema) plan)
        right.selectionSet) = .ok (rightFields, 0) := by
    simpa [hroot] using hright
  have hrightFieldsEq : rightFields = collectedRightFields :=
    executeAnnotatedCollectedFields_success_unique schema
      (spineResolvers schema) (coerceVariableValues right suppliedValues)
      (.object (left.rootType schema) plan)
      (collectFields schema (coerceVariableValues right suppliedValues)
        (right.rootType schema) (.object (left.rootType schema) plan)
        right.selectionSet) hright' hrightCollected
  simpa [hleftFieldsEq, hrightFieldsEq] using hoperationIncludes

private theorem object_getPossibleTypes_eq_singleton
    (schema : Schema) {typeName : Name} (hobject : schema.objectType typeName)
    : schema.getPossibleTypes typeName = [typeName] := by
  rcases hobject with ⟨objectType, hlookup⟩
  have hname : objectType.name = typeName := by
    have hmatch := List.find?_some hlookup
    simpa [Schema.lookupType, TypeDefinition.name] using hmatch
  simp [Schema.getPossibleTypes, hlookup, hname]

private theorem executableGroupNamesNodup_map
    : ∀ groups : List (Name × List ExecutableField),
        NormalForm.executableGroupNamesNodup groups -> (groups.map Prod.fst).Nodup
  | [], _hnodup => by simp
  | (responseName, fields) :: rest, hnodup => by
      rw [List.map_cons, List.nodup_cons]
      exact ⟨hnodup.1, executableGroupNamesNodup_map rest hnodup.2⟩

private theorem spineSelectionExecution_success
    (schema : Schema) (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (variableValues : VariableValues) (runtimeType : Name)
    (selectionSet : List Selection)
    (hobject : schema.objectType runtimeType)
    (hready : NormalForm.selectionSetSemanticsReady schema runtimeType selectionSet)
    (hcoercion
      : selectionSetArgumentsCoercible schema variableValues runtimeType selectionSet)
    (hinhabited
      : selectionSetCompositeFieldTypesInhabited schema runtimeType selectionSet)
    (hmerge : FieldMerge.fieldsInSetCanMerge schema runtimeType selectionSet)
    (plan : RuntimePlan)
    : ∃ fields,
        executeQueryAnnotatedCollectedFields schema
          (spineResolvers schema) variableValues
          (responseDepthFuelBound schema (selectionSetResponseDepth selectionSet))
          (.object runtimeType plan)
          (collectFields schema variableValues runtimeType
            (.object runtimeType plan) selectionSet)
        = .ok (fields, 0) := by
  exact executeQueryAnnotatedCollectedFields_supported schema
    (spineResolvers schema) variableValues hschema
    (spineResolvers_supported schema) runtimeType plan selectionSet
    hobject hready hcoercion hinhabited hmerge _ (Nat.le_refl _)

noncomputable def runtimePlanHead (schema : Schema) (targetType runtimeType : Name)
    : Name -> Name :=
  fun typeName =>
    if typeName = targetType then
      runtimeType
    else
      representativePossibleObject schema typeName

private theorem runtimePlanHead_valid
    (schema : Schema) (targetType runtimeType : Name)
    (hruntime : runtimeType ∈ schema.getPossibleTypes targetType)
    : ∀ typeName,
        schema.getPossibleTypes typeName ≠ []
        -> runtimePlanHead schema targetType runtimeType typeName
            ∈ schema.getPossibleTypes typeName := by
  intro typeName hpossible
  classical
  by_cases heq : typeName = targetType
  · subst typeName
    simpa [runtimePlanHead] using hruntime
  · simp [runtimePlanHead, heq,
      representativePossibleObject_mem schema typeName hpossible]

@[simp]
private theorem runtimePlanHead_target (schema : Schema) (targetType runtimeType : Name)
    : runtimePlanHead schema targetType runtimeType targetType = runtimeType := by
  classical
  simp [runtimePlanHead]

private theorem spineSelectionIncludes_group_match
    (schema : Schema) (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (leftValues rightValues : VariableValues) (runtimeType : Name)
    (leftSelectionSet rightSelectionSet : List Selection)
    (hobject : schema.objectType runtimeType)
    (hleftReady
      : NormalForm.selectionSetSemanticsReady schema runtimeType leftSelectionSet)
    (hleftCoercion
      : selectionSetArgumentsCoercible schema leftValues runtimeType leftSelectionSet)
    (hleftInhabited
      : selectionSetCompositeFieldTypesInhabited schema runtimeType leftSelectionSet)
    (hleftMerge : FieldMerge.fieldsInSetCanMerge schema runtimeType leftSelectionSet)
    (hrightReady
      : NormalForm.selectionSetSemanticsReady schema runtimeType rightSelectionSet)
    (hrightCoercion
      : selectionSetArgumentsCoercible schema rightValues runtimeType rightSelectionSet)
    (hrightInhabited
      : selectionSetCompositeFieldTypesInhabited schema runtimeType rightSelectionSet)
    (hrightMerge : FieldMerge.fieldsInSetCanMerge schema runtimeType rightSelectionSet)
    (hincludes
      : SpineSelectionIncludes schema leftValues rightValues
          runtimeType runtimeType leftSelectionSet rightSelectionSet)
    {rightName : Name} {rightFields : List ExecutableField}
    (hrightGroup
      : (rightName, rightFields)
        ∈ collectFields schema rightValues runtimeType
            (.object runtimeType (defaultRuntimePlan schema))
            rightSelectionSet)
    : ∃ leftField leftRest rightField rightRest definition,
        (rightName, leftField :: leftRest)
          ∈ collectFields schema leftValues runtimeType
              (.object runtimeType (defaultRuntimePlan schema))
              leftSelectionSet
        ∧ rightFields = rightField :: rightRest
        ∧ leftField.parentType = rightField.parentType
        ∧ leftField.fieldName = rightField.fieldName
        ∧ Argument.argumentsEquivalent leftField.arguments rightField.arguments
        ∧ schema.lookupField rightField.parentType rightField.fieldName
          = some definition := by
  let plan := defaultRuntimePlan schema
  have hplan : plan.Valid schema := defaultRuntimePlan_valid schema
  rcases spineSelectionExecution_success schema hschema leftValues runtimeType
      leftSelectionSet hobject hleftReady hleftCoercion hleftInhabited hleftMerge plan with
    ⟨leftResponseFields, hleftResult⟩
  rcases spineSelectionExecution_success schema hschema rightValues runtimeType
      rightSelectionSet hobject hrightReady hrightCoercion hrightInhabited hrightMerge plan with
    ⟨rightResponseFields, hrightResult⟩
  have hresponseIncludes := hincludes plan hplan _ _ _ _ hleftResult hrightResult
  rcases executeAnnotatedCollectedFields_group_annotation schema
      (spineResolvers schema) rightValues _ (.object runtimeType plan)
      (collectFields schema rightValues runtimeType (.object runtimeType plan)
        rightSelectionSet) rightResponseFields hrightResult
      (by simpa [plan] using hrightGroup) with
    ⟨rightCompletionFuel, rightField, rightRest, definition, rightResolved,
      rightValue, _hrightFuel, hrightFields, hrightLookup, _hrightResolve,
      _hrightComplete, hrightMember⟩
  simp only [annotatedResponseValueIncludes] at hresponseIncludes
  rcases hresponseIncludes rightName
      (resolvedFieldProvenance schema rightValues definition rightField)
      rightValue hrightMember with
    ⟨leftName, leftCall, leftValue, hleftMember, hleftName, hcall,
      _hvalueIncludes⟩
  rcases executeAnnotatedCollectedFields_field_origin schema
      (spineResolvers schema) leftValues _ (.object runtimeType plan)
      (collectFields schema leftValues runtimeType (.object runtimeType plan)
        leftSelectionSet) leftResponseFields hleftResult hleftMember with
    ⟨originName, originFields, groupResponseFields, horiginGroup,
      horiginResult, horiginMember⟩
  rcases executeAnnotatedField_ok_zero_decompose schema
      (spineResolvers schema) leftValues _ (.object runtimeType plan)
      originName originFields groupResponseFields horiginResult with
    ⟨leftCompletionFuel, leftField, leftRest, leftDefinition, leftResolved,
      originValue, _hleftFuel, horiginFields, _hleftLookup, _hleftResolve,
      _hleftComplete, hgroupResponse⟩
  rw [hgroupResponse] at horiginMember
  simp only [List.mem_singleton] at horiginMember
  injection horiginMember with hnameEq hcallEq hvalueEq
  have horiginNameEq : originName = rightName := hnameEq.symm.trans hleftName
  subst leftName
  subst leftCall
  subst leftValue
  subst originName
  subst originFields
  rcases hcall with ⟨hparent, hfield, harguments⟩
  simp only [resolvedFieldProvenance] at hparent hfield harguments
  exact ⟨leftField, leftRest, rightField, rightRest, definition,
    by simpa [plan] using horiginGroup, hrightFields, hparent, hfield,
    harguments, hrightLookup⟩

private theorem spineSelectionIncludes_child
    (schema : Schema) (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (leftValues rightValues : VariableValues) (runtimeType : Name)
    (leftSelectionSet rightSelectionSet : List Selection)
    (hobject : schema.objectType runtimeType)
    (hleftReady
      : NormalForm.selectionSetSemanticsReady schema runtimeType leftSelectionSet)
    (hleftCoercion
      : selectionSetArgumentsCoercible schema leftValues runtimeType leftSelectionSet)
    (hleftInhabited
      : selectionSetCompositeFieldTypesInhabited schema runtimeType leftSelectionSet)
    (hleftMerge : FieldMerge.fieldsInSetCanMerge schema runtimeType leftSelectionSet)
    (hrightReady
      : NormalForm.selectionSetSemanticsReady schema runtimeType rightSelectionSet)
    (hrightCoercion
      : selectionSetArgumentsCoercible schema rightValues runtimeType rightSelectionSet)
    (hrightInhabited
      : selectionSetCompositeFieldTypesInhabited schema runtimeType rightSelectionSet)
    (hrightMerge : FieldMerge.fieldsInSetCanMerge schema runtimeType rightSelectionSet)
    (hincludes
      : SpineSelectionIncludes schema leftValues rightValues
          runtimeType runtimeType leftSelectionSet rightSelectionSet)
    (responseName : Name)
    (leftField rightField : ExecutableField)
    (leftRest rightRest : List ExecutableField)
    (definition : FieldDefinition)
    (hleftGroup
      : (responseName, leftField :: leftRest)
        ∈ collectFields schema leftValues runtimeType
            (.object runtimeType (defaultRuntimePlan schema))
            leftSelectionSet)
    (hrightGroup
      : (responseName, rightField :: rightRest)
        ∈ collectFields schema rightValues runtimeType
            (.object runtimeType (defaultRuntimePlan schema))
            rightSelectionSet)
    (hparent : leftField.parentType = rightField.parentType)
    (hfield : leftField.fieldName = rightField.fieldName)
    (hlookup
      : schema.lookupField rightField.parentType rightField.fieldName = some definition)
    (hcomposite : definition.outputType.isCompositeBool schema = true)
    (childRuntimeType : Name)
    (hchildRuntime
      : childRuntimeType ∈ schema.getPossibleTypes definition.outputType.namedType)
    : SpineSelectionIncludes schema leftValues rightValues
        childRuntimeType childRuntimeType
        (mergedFieldSelectionSet (leftField :: leftRest))
        (mergedFieldSelectionSet (rightField :: rightRest)) := by
  intro childPlan hchildPlan leftFuel rightFuel leftResponseFields
    rightResponseFields hleftChild hrightChild
  let head := runtimePlanHead schema definition.outputType.namedType
    childRuntimeType
  let parentPlan := RuntimePlan.cons head childPlan
  have hheadValid : ∀ typeName,
      schema.getPossibleTypes typeName ≠ []
      -> head typeName ∈ schema.getPossibleTypes typeName := by
    exact runtimePlanHead_valid schema definition.outputType.namedType
      childRuntimeType hchildRuntime
  have hparentPlan : parentPlan.Valid schema :=
    RuntimePlan.Valid.cons hheadValid hchildPlan
  have htarget : parentPlan 0 definition.outputType.namedType = childRuntimeType := by
    simp [parentPlan, head, RuntimePlan.cons, runtimePlanHead_target]
  have hshift : parentPlan.shift = childPlan := by
    simp [parentPlan]
  rcases spineSelectionExecution_success schema hschema leftValues runtimeType
      leftSelectionSet hobject hleftReady hleftCoercion hleftInhabited hleftMerge
      parentPlan with
    ⟨parentLeftResponse, hparentLeft⟩
  rcases spineSelectionExecution_success schema hschema rightValues runtimeType
      rightSelectionSet hobject hrightReady hrightCoercion hrightInhabited hrightMerge
      parentPlan with
    ⟨parentRightResponse, hparentRight⟩
  have hparentResponseIncludes := hincludes parentPlan hparentPlan _ _ _ _
    hparentLeft hparentRight
  have hleftGroup' :
      (responseName, leftField :: leftRest) ∈
        collectFields schema leftValues runtimeType (.object runtimeType parentPlan)
          leftSelectionSet := by
    rw [← collectFields_object_ref_irrelevant schema leftValues runtimeType
      runtimeType (defaultRuntimePlan schema) parentPlan leftSelectionSet]
    exact hleftGroup
  have hrightGroup' :
      (responseName, rightField :: rightRest) ∈
        collectFields schema rightValues runtimeType (.object runtimeType parentPlan)
          rightSelectionSet := by
    rw [← collectFields_object_ref_irrelevant schema rightValues runtimeType
      runtimeType (defaultRuntimePlan schema) parentPlan rightSelectionSet]
    exact hrightGroup
  rcases executeAnnotatedCollectedFields_group_annotation schema
      (spineResolvers schema) rightValues _ (.object runtimeType parentPlan)
      (collectFields schema rightValues runtimeType (.object runtimeType parentPlan)
        rightSelectionSet) parentRightResponse hparentRight hrightGroup' with
    ⟨rightCompletionFuel, rightRepresentative, rightTail, rightDefinition,
      rightResolved, rightValue, _hrightFuel, hrightFields, hrightLookup,
      hrightResolve, hrightComplete, hrightMember⟩
  injection hrightFields with hrightHeadEq hrightTailEq
  subst rightRepresentative
  subst rightTail
  rw [hlookup] at hrightLookup
  injection hrightLookup with hrightDefinitionEq
  subst rightDefinition
  have hrightResolvedValue :
      rightResolved = spineResolverValue schema parentPlan
        definition.outputType := by
    symm
    cases hcoercion
          : coerceArgumentValues schema rightValues definition.arguments
              rightField.arguments with
    | error =>
        simp [hcoercion] at hrightResolve
    | success coercedArguments =>
        simpa [resolveFieldValue, spineResolvers, hlookup, hcoercion] using hrightResolve
  subst rightResolved
  simp only [annotatedResponseValueIncludes] at hparentResponseIncludes
  rcases hparentResponseIncludes responseName
      (resolvedFieldProvenance schema rightValues definition rightField) rightValue
      hrightMember with
    ⟨matchedName, matchedCall, matchedValue, hmatchedMember, hmatchedName,
      _hmatchedCall, hmatchedValue⟩
  rcases executeAnnotatedCollectedFields_field_origin schema
      (spineResolvers schema) leftValues _ (.object runtimeType parentPlan)
      (collectFields schema leftValues runtimeType (.object runtimeType parentPlan)
        leftSelectionSet) parentLeftResponse hparentLeft hmatchedMember with
    ⟨originName, originFields, originResponseFields, horiginGroup,
      horiginResult, horiginMember⟩
  have horiginName : originName = responseName := by
    have hresponseNames := collectFields_responseName schema leftValues runtimeType
      (.object runtimeType parentPlan) leftSelectionSet originName originFields
      horiginGroup
    have horiginAnnotationName : originName = matchedName := by
      rcases executeAnnotatedField_ok_zero_decompose schema
          (spineResolvers schema) leftValues _
          (.object runtimeType parentPlan) originName originFields originResponseFields
          horiginResult with
        ⟨originFuel, originField, originRest, originDefinition, originResolved,
          originValue, _hfuel, _hfields, _hlookup, _hresolve, _hcomplete,
          horiginResponse⟩
      rw [horiginResponse] at horiginMember
      simp only [List.mem_singleton] at horiginMember
      injection horiginMember with hnameEq hcallEq hvalueEq
      exact hnameEq.symm
    exact horiginAnnotationName.trans hmatchedName
  have hgroupsEq :
      (originName, originFields) = (responseName, leftField :: leftRest) :=
    pair_eq_of_map_fst_nodup
      (executableGroupNamesNodup_map _
        (NormalForm.collectFields_namesNodup schema leftValues runtimeType
          (.object runtimeType parentPlan) leftSelectionSet))
      horiginGroup hleftGroup' horiginName
  injection hgroupsEq with _horiginNameEq horiginFieldsEq
  subst originFields
  rcases executeAnnotatedField_ok_zero_decompose schema
      (spineResolvers schema) leftValues _ (.object runtimeType parentPlan)
      originName (leftField :: leftRest) originResponseFields horiginResult with
    ⟨leftCompletionFuel, leftRepresentative, leftTail, leftDefinition,
      leftResolved, leftValue, _hleftFuel, hleftFields, hleftLookup,
      hleftResolve, hleftComplete, hleftResponse⟩
  injection hleftFields with hleftHeadEq hleftTailEq
  subst leftRepresentative
  subst leftTail
  have hleftLookup' :
      schema.lookupField leftField.parentType leftField.fieldName = some definition := by
    simpa [hparent, hfield] using hlookup
  rw [hleftLookup'] at hleftLookup
  injection hleftLookup with hleftDefinitionEq
  subst leftDefinition
  have hleftResolvedValue :
      leftResolved = spineResolverValue schema parentPlan
        definition.outputType := by
    symm
    cases hcoercion
          : coerceArgumentValues schema leftValues definition.arguments
              leftField.arguments with
    | error =>
        simp [hcoercion] at hleftResolve
    | success coercedArguments =>
        simpa [resolveFieldValue, spineResolvers, hleftLookup', hcoercion] using hleftResolve
  subst leftResolved
  rw [hleftResponse] at horiginMember
  simp only [List.mem_singleton] at horiginMember
  injection horiginMember with horiginResponseNameEq horiginCallEq horiginValueEq
  have hwrappedIncludes : annotatedResponseValueIncludes leftValue rightValue := by
    rw [← horiginValueEq]
    exact hmatchedValue
  have hpossible : schema.getPossibleTypes definition.outputType.namedType ≠ [] := by
    intro hempty
    rw [hempty] at hchildRuntime
    simp at hchildRuntime
  rcases completeSpineValue_composite_decompose schema parentPlan hparentPlan
      leftValues leftCompletionFuel definition.outputType (leftField :: leftRest)
      leftValue hcomposite hpossible hleftComplete with
    ⟨actualLeftFuel, actualLeftFields, hactualLeft, hleftValue⟩
  rcases completeSpineValue_composite_decompose schema parentPlan hparentPlan
      rightValues rightCompletionFuel definition.outputType (rightField :: rightRest)
      rightValue hcomposite hpossible hrightComplete with
    ⟨actualRightFuel, actualRightFields, hactualRight, hrightValue⟩
  rw [hleftValue, hrightValue] at hwrappedIncludes
  have hactualIncludes := annotatedResponseValueIncludes_wrapComposite definition.outputType
    (.object (parentPlan 0 definition.outputType.namedType) actualLeftFields)
    (.object (parentPlan 0 definition.outputType.namedType) actualRightFields)
    hwrappedIncludes
  have hactualLeft' : executeQueryAnnotatedCollectedFields schema
      (spineResolvers schema) leftValues actualLeftFuel
      (.object childRuntimeType childPlan)
      (collectFields schema leftValues childRuntimeType
        (.object childRuntimeType childPlan)
        (mergedFieldSelectionSet (leftField :: leftRest)))
      = .ok (actualLeftFields, 0) := by
    simpa [NormalForm.collectSubfields_eq_collectFields_mergedFieldSelectionSet,
      htarget, hshift] using hactualLeft
  have hactualRight' : executeQueryAnnotatedCollectedFields schema
      (spineResolvers schema) rightValues actualRightFuel
      (.object childRuntimeType childPlan)
      (collectFields schema rightValues childRuntimeType
        (.object childRuntimeType childPlan)
        (mergedFieldSelectionSet (rightField :: rightRest)))
      = .ok (actualRightFields, 0) := by
    simpa [NormalForm.collectSubfields_eq_collectFields_mergedFieldSelectionSet,
      htarget, hshift] using hactualRight
  have hleftEq : leftResponseFields = actualLeftFields :=
    executeAnnotatedCollectedFields_success_unique schema
      (spineResolvers schema) leftValues (.object childRuntimeType childPlan)
      (collectFields schema leftValues childRuntimeType
        (.object childRuntimeType childPlan)
        (mergedFieldSelectionSet (leftField :: leftRest))) hleftChild hactualLeft'
  have hrightEq : rightResponseFields = actualRightFields :=
    executeAnnotatedCollectedFields_success_unique schema
      (spineResolvers schema) rightValues (.object childRuntimeType childPlan)
      (collectFields schema rightValues childRuntimeType
        (.object childRuntimeType childPlan)
        (mergedFieldSelectionSet (rightField :: rightRest))) hrightChild hactualRight'
  simpa [hleftEq, hrightEq, htarget] using hactualIncludes

set_option maxRecDepth 10000 in
theorem spineSelectionIncludes_selectionSetIncludesBoolWithFuel
    (schema : Schema) (hschema : SchemaWellFormedness.schemaWellFormed schema)
    : ∀ fuel leftValues rightValues runtimeType leftSelectionSet rightSelectionSet,
        (∀ variableName,
          variableName
            ∈ SelectionConditions.selectionSetBooleanVariables rightSelectionSet
          -> inputValueBoolean? leftValues (.variable variableName)
              = inputValueBoolean? rightValues (.variable variableName))
        -> schema.objectType runtimeType
        -> NormalForm.selectionSetSemanticsReady schema runtimeType leftSelectionSet
        -> selectionSetArgumentsCoercible schema leftValues runtimeType leftSelectionSet
        -> selectionSetCompositeFieldTypesInhabited schema runtimeType leftSelectionSet
        -> FieldMerge.fieldsInSetCanMerge schema runtimeType leftSelectionSet
        -> NormalForm.selectionSetSemanticsReady schema runtimeType rightSelectionSet
        -> selectionSetArgumentsCoercible schema rightValues runtimeType rightSelectionSet
        -> selectionSetCompositeFieldTypesInhabited schema runtimeType rightSelectionSet
        -> FieldMerge.fieldsInSetCanMerge schema runtimeType rightSelectionSet
        -> SpineSelectionIncludes schema leftValues rightValues
            runtimeType runtimeType leftSelectionSet rightSelectionSet
        -> selectionSetResponseDepth rightSelectionSet < fuel
        -> selectionSetIncludesBoolWithFuel schema fuel runtimeType leftValues
              leftSelectionSet rightSelectionSet
            = true := by
  intro fuel
  induction fuel with
  | zero =>
      intro leftValues rightValues runtimeType leftSelectionSet rightSelectionSet
        _hboolean _hobject _hleftReady _hleftCoercion _hleftInhabited _hleftMerge
        _hrightReady _hrightCoercion _hrightInhabited _hrightMerge _hincludes hdepth
      omega
  | succ fuel ih =>
      intro leftValues rightValues runtimeType leftSelectionSet rightSelectionSet
        hboolean hobject hleftReady hleftCoercion hleftInhabited hleftMerge hrightReady
        hrightCoercion hrightInhabited hrightMerge hincludes hdepth
      have hpossible := object_getPossibleTypes_eq_singleton schema hobject
      simp only [selectionSetIncludesBoolWithFuel, selectionSetIncludesAtRuntimeBoolWithFuel,
        hpossible, List.all_cons, List.all_nil, Bool.and_true]
      apply List.all_eq_true.mpr
      intro rightGroup hrightGroup
      rcases rightGroup with ⟨rightName, rightFields⟩
      have hrightGroup' :
          (rightName, rightFields) ∈
            collectRuntimeFieldGroups schema rightValues runtimeType runtimeType
              rightSelectionSet := by
        rw [← collectRuntimeFieldGroups_eq_of_boolean_agreement schema leftValues
          rightValues runtimeType runtimeType rightSelectionSet (by
            intro variableName hvariable
            rw [hboolean variableName hvariable])]
        exact hrightGroup
      have hrightGroupDefault :
          (rightName, rightFields) ∈
            collectFields schema rightValues runtimeType
              (.object runtimeType (defaultRuntimePlan schema))
              rightSelectionSet := by
        rw [← collectRuntimeFieldGroups_eq_collectFields_object schema rightValues
          runtimeType runtimeType (defaultRuntimePlan schema)
          rightSelectionSet]
        exact hrightGroup'
      rcases spineSelectionIncludes_group_match schema hschema leftValues rightValues
          runtimeType leftSelectionSet rightSelectionSet hobject hleftReady hleftCoercion
          hleftInhabited hleftMerge hrightReady hrightCoercion hrightInhabited hrightMerge
          hincludes
          hrightGroupDefault with
        ⟨leftField, leftRest, rightField, rightRest, definition, hleftGroupDefault,
          hrightFields, hparent, hfield, harguments, hlookup⟩
      subst rightFields
      have hleftGroup :
          (rightName, leftField :: leftRest) ∈
            collectRuntimeFieldGroups schema leftValues runtimeType runtimeType
              leftSelectionSet := by
        rw [collectRuntimeFieldGroups_eq_collectFields_object schema leftValues
          runtimeType runtimeType (defaultRuntimePlan schema)
          leftSelectionSet]
        exact hleftGroupDefault
      apply List.any_eq_true.mpr
      refine ⟨(rightName, leftField :: leftRest), hleftGroup, ?_⟩
      simp only [beq_self_eq_true, Bool.true_and, Bool.and_eq_true]
      refine ⟨⟨⟨beq_iff_eq.mpr hparent, beq_iff_eq.mpr hfield⟩,
        (argumentsSyntacticallyEquivalentBool_iff _ _).mpr harguments⟩, ?_⟩
      rw [hlookup]
      by_cases hcomposite : definition.outputType.isCompositeBool schema = true
      · simp only [hcomposite, if_true, List.all_eq_true]
        intro childRuntimeType hchildRuntime
        have hchildObject : schema.objectType childRuntimeType :=
          SchemaWellFormedness.schemaWellFormed_possibleTypesAreObjects hschema
            definition.outputType.namedType childRuntimeType hchildRuntime
        have hleftGroupsReady := executableGroupsReady_collectFields schema leftValues
          runtimeType (defaultRuntimePlan schema) leftSelectionSet hobject
          hleftReady hleftInhabited hleftMerge
        have hrightGroupsReady := executableGroupsReady_collectFields schema rightValues
          runtimeType (defaultRuntimePlan schema) rightSelectionSet hobject
          hrightReady hrightInhabited hrightMerge
        have hleftGroupsCoercion :=
          executableGroupsArgumentCoercionReady_collectFields schema leftValues
            runtimeType (defaultRuntimePlan schema) leftSelectionSet hobject
            hleftReady hleftCoercion
        have hrightGroupsCoercion :=
          executableGroupsArgumentCoercionReady_collectFields schema rightValues
            runtimeType (defaultRuntimePlan schema) rightSelectionSet hobject
            hrightReady hrightCoercion
        have hleftFieldsReady := hleftGroupsReady rightName (leftField :: leftRest)
          hleftGroupDefault
        have hrightFieldsReady := hrightGroupsReady rightName (rightField :: rightRest)
          hrightGroupDefault
        have hleftFieldsCoercion := hleftGroupsCoercion rightName
          (leftField :: leftRest) hleftGroupDefault
        have hrightFieldsCoercion := hrightGroupsCoercion rightName
          (rightField :: rightRest) hrightGroupDefault
        have hleftLookup : schema.lookupField leftField.parentType leftField.fieldName
            = some definition := by
          simpa [hparent, hfield] using hlookup
        have hleftCompletionReady : completionFieldsReady schema
            definition.outputType (leftField :: leftRest) :=
          ⟨hleftFieldsReady, leftField, definition, by simp, hleftLookup, rfl⟩
        have hrightCompletionReady : completionFieldsReady schema
            definition.outputType (rightField :: rightRest) :=
          ⟨hrightFieldsReady, rightField, definition, by simp, hlookup, rfl⟩
        have hchildIncludesBool :
            schema.typeIncludesObjectBool definition.outputType.namedType
              childRuntimeType = true :=
          List.contains_iff_mem.mpr hchildRuntime
        have hleftChildReady := completionFieldsReady_merged_semantics
          hleftCompletionReady hchildIncludesBool
        have hrightChildReady := completionFieldsReady_merged_semantics
          hrightCompletionReady hchildIncludesBool
        have hleftChildCoercion := completionFieldsReady_merged_argumentCoercion
          hleftCompletionReady hleftFieldsCoercion hchildIncludesBool
        have hrightChildCoercion := completionFieldsReady_merged_argumentCoercion
          hrightCompletionReady hrightFieldsCoercion hchildIncludesBool
        have hleftChildInhabited := completionFieldsReady_merged_inhabited
          hleftCompletionReady hchildIncludesBool
        have hrightChildInhabited := completionFieldsReady_merged_inhabited
          hrightCompletionReady hchildIncludesBool
        have hleftChildMerge := completionFieldsReady_merged_canMerge
          hleftCompletionReady childRuntimeType
        have hrightChildMerge := completionFieldsReady_merged_canMerge
          hrightCompletionReady childRuntimeType
        have hchildIncludes := spineSelectionIncludes_child schema hschema
          leftValues rightValues runtimeType leftSelectionSet rightSelectionSet hobject
          hleftReady hleftCoercion hleftInhabited hleftMerge hrightReady hrightCoercion
          hrightInhabited hrightMerge hincludes rightName leftField rightField leftRest
          rightRest definition
          hleftGroupDefault hrightGroupDefault hparent hfield hlookup hcomposite
          childRuntimeType hchildRuntime
        have hrightGroupDepth :
            ∀ field, field ∈ rightField :: rightRest
              -> selectionSetResponseDepth field.selectionSet + 1
                ≤ selectionSetResponseDepth rightSelectionSet := by
          intro field hfieldMember
          exact collectFields_responseDepth_bound schema rightValues runtimeType
            (.object runtimeType (defaultRuntimePlan schema))
            rightSelectionSet field
            (by
              rw [← Execution.FieldGroups.flattenCollectedFields_eq_flatMap_snd]
              exact (Execution.FieldGroups.mem_flattenCollectedFields_iff _ _).mpr
                ⟨rightName, rightField :: rightRest, hrightGroupDefault,
                  hfieldMember⟩)
        have hrightChildDepth :
            selectionSetResponseDepth (mergedFieldSelectionSet
              (rightField :: rightRest))
              < fuel := by
          have hparentDepthPositive : 0 < selectionSetResponseDepth rightSelectionSet := by
            have := hrightGroupDepth rightField (by simp)
            omega
          have hmerged : selectionSetResponseDepth
              (mergedFieldSelectionSet (rightField :: rightRest))
              ≤ selectionSetResponseDepth rightSelectionSet - 1 := by
            rw [Execution.FieldGroups.mergedFieldSelectionSet_eq_flatMap]
            apply selectionSetResponseDepth_flatMap_le (rightField :: rightRest)
              (selectionSetResponseDepth rightSelectionSet - 1)
            intro field hfieldMember
            have := hrightGroupDepth field hfieldMember
            omega
          omega
        have hchildBooleanAgreement : ∀ variableName,
            variableName
              ∈ SelectionConditions.selectionSetBooleanVariables
                  (mergedFieldSelectionSet (rightField :: rightRest))
            -> inputValueBoolean? leftValues (.variable variableName)
                = inputValueBoolean? rightValues (.variable variableName) := by
          intro variableName hvariable
          apply hboolean variableName
          apply mergedSelectionSet_variables_within_of_group_mem schema rightValues
            runtimeType runtimeType rightSelectionSet
              (rightName, rightField :: rightRest) hrightGroup'
          simpa [executableFieldsMergedSelectionSet_eq_mergedFieldSelectionSet] using
            hvariable
        have hchildCheck := ih leftValues rightValues childRuntimeType
            (mergedFieldSelectionSet (leftField :: leftRest))
            (mergedFieldSelectionSet (rightField :: rightRest))
            hchildBooleanAgreement hchildObject
            hleftChildReady hleftChildCoercion hleftChildInhabited hleftChildMerge
            hrightChildReady hrightChildCoercion hrightChildInhabited hrightChildMerge
            hchildIncludes hrightChildDepth
        rw [selectionSetIncludesBoolWithFuel.eq_def, List.all_eq_true] at hchildCheck
        simpa [executableFieldsMergedSelectionSet_eq_mergedFieldSelectionSet] using
          hchildCheck
      · have hleaf : definition.outputType.isCompositeBool schema = false := by
          simpa using hcomposite
        simp [hleaf]

theorem includesBool_complete {schema : Schema} {left right : Operation}
    : IncludesBoolComplete schema left right := by
  intro hschema hleftValid hrightValid hleftInhabited hrightInhabited hprobes
    hincludes
  have hroot := valid_operations_rootType_eq hleftValid hrightValid
  have hdefinitionsBool : sharedVariableDefinitionsSyntacticallyCompatibleBool
      left.variableDefinitions right.variableDefinitions = true :=
    (sharedVariableDefinitionsSyntacticallyCompatibleBool_iff _ _).mpr hincludes.1
  have hguard : ((left.rootType schema == right.rootType schema)
      && sharedVariableDefinitionsSyntacticallyCompatibleBool
        left.variableDefinitions right.variableDefinitions) = true := by
    simp [hroot, hdefinitionsBool]
  apply includesBool_complete_of_reference hschema hleftValid
    hrightValid hleftInhabited hrightInhabited
  unfold includesBoolReference
  rw [if_pos hguard]
  apply List.all_eq_true.mpr
  intro conditionValues hconditionValues
  let variables := comparisonConditionVariables left.selectionSet right.selectionSet
  rcases hprobes conditionValues (by simpa only [variables] using hconditionValues) with
    ⟨remainingValues, hleftArgumentReady', hrightArgumentReady'⟩
  let probeValues := conditionValues ++ remainingValues
  have hleftArgumentReady : operationArgumentsCoercible schema probeValues left := by
    simpa only [probeValues] using hleftArgumentReady'
  have hrightArgumentReady : operationArgumentsCoercible schema probeValues right := by
    simpa only [probeValues] using hrightArgumentReady'
  have hconditionAgreement (operation : Operation) : ∀ variableName,
      variableName ∈ comparisonConditionVariables left.selectionSet right.selectionSet
      -> inputValueBoolean? conditionValues (.variable variableName)
          = inputValueBoolean? (coerceVariableValues operation probeValues)
              (.variable variableName) := by
    intro variableName hvariable
    rcases booleanVariableAssignments_lookup variables conditionValues hconditionValues
        variableName (by simpa [variables] using hvariable) with ⟨value, hlookup⟩
    have hconditionBoolean : inputValueBoolean? conditionValues
        (.variable variableName) = some value := by
      simp [inputValueBoolean?, hlookup, ConstInputValue.toInputValue,
        InputValue.staticBoolean?]
    have hprobeBoolean : inputValueBoolean? probeValues
        (.variable variableName) = some value := by
      simp [probeValues, inputValueBoolean?, lookupVariableValue?_append, hlookup,
        ConstInputValue.toInputValue, InputValue.staticBoolean?]
    have hcoercedBoolean :=
      NormalForm.CompleteNormalization.inputValueBoolean?_coerceVariableValues_eq_some
        operation probeValues hprobeBoolean
    exact hconditionBoolean.trans hcoercedBoolean.symm
  have hbooleanAgreement : ∀ variableName,
      variableName
        ∈ SelectionConditions.selectionSetBooleanVariables right.selectionSet
      -> inputValueBoolean? (coerceVariableValues left probeValues)
            (.variable variableName)
          = inputValueBoolean? (coerceVariableValues right probeValues)
              (.variable variableName) := by
    intro variableName hvariable
    have hcomparison : variableName
        ∈ comparisonConditionVariables left.selectionSet right.selectionSet := by
      simp [comparisonConditionVariables, hvariable]
    exact (hconditionAgreement left variableName hcomparison).symm.trans
      (hconditionAgreement right variableName hcomparison)
  have hleftObject : schema.objectType (left.rootType schema) :=
    NormalForm.CompleteNormalization.operation_root_object_of_valid hschema hleftValid
  have hleftReady : NormalForm.selectionSetSemanticsReady schema
      (left.rootType schema) left.selectionSet :=
    NormalForm.CompleteNormalization.operation_selectionSetSemanticsReady_of_valid
      hschema hleftValid
  have hleftMerge : FieldMerge.fieldsInSetCanMerge schema (left.rootType schema)
      left.selectionSet :=
    Validation.operationDefinitionValid_fieldsInSetCanMerge hleftValid
  have hrightReady : NormalForm.selectionSetSemanticsReady schema
      (left.rootType schema) right.selectionSet := by
    rw [hroot]
    exact
      NormalForm.CompleteNormalization.operation_selectionSetSemanticsReady_of_valid
        hschema hrightValid
  have hrightMerge : FieldMerge.fieldsInSetCanMerge schema (left.rootType schema)
      right.selectionSet := by
    rw [hroot]
    exact Validation.operationDefinitionValid_fieldsInSetCanMerge hrightValid
  have hrightInhabitedRoot : selectionSetCompositeFieldTypesInhabited schema
      (left.rootType schema) right.selectionSet := by
    rw [hroot]
    exact hrightInhabited
  have hspine := includes_root_spineSelectionIncludes hschema hleftValid hrightValid
    hleftInhabited hrightInhabited hincludes probeValues hleftArgumentReady
    hrightArgumentReady
  have hdepth : selectionSetResponseDepth right.selectionSet < right.size + 1 := by
    have := selectionSetResponseDepth_le_size right.selectionSet
    simp only [Operation.size]
    omega
  have hcoercedCheck :=
    spineSelectionIncludes_selectionSetIncludesBoolWithFuel schema hschema
      (right.size + 1) (coerceVariableValues left probeValues)
    (coerceVariableValues right probeValues) (left.rootType schema)
    left.selectionSet right.selectionSet hbooleanAgreement hleftObject hleftReady
    (by simpa [operationArgumentsCoercible] using hleftArgumentReady)
    hleftInhabited hleftMerge hrightReady
    (by
      rw [hroot]
      simpa [operationArgumentsCoercible] using hrightArgumentReady)
    hrightInhabitedRoot hrightMerge hspine hdepth
  have hagreement := selectionSetIncludesBoolWithFuel_eq_of_boolean_agreement schema
    (right.size + 1) (left.rootType schema) conditionValues
    (coerceVariableValues left probeValues) left.selectionSet right.selectionSet
    (by
      intro variableName hvariable
      rw [hconditionAgreement left variableName
        (by simp [comparisonConditionVariables, hvariable])])
    (by
      intro variableName hvariable
      rw [hconditionAgreement left variableName
        (by simp [comparisonConditionVariables, hvariable])])
  rw [← hroot, hagreement]
  exact hcoercedCheck

end QueryInclusion
end GraphQL
