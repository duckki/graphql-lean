import Proofs.GraphQL.Algorithms.ExecutionBreadth.Semantics.Resolver
import Proofs.GraphQL.Algorithms.ExecutionBreadth.Semantics.Invariants

/-!
Slot-construction and completion lemmas for the current positional stack machine.

The important change from the earlier model is that child object values are no longer
popped by a second completion key. Field blocks stay keyed by `ScheduleKey`, but child
values are consumed positionally by `ValueSlot.child`.
-/

namespace GraphQL

namespace Algorithms
namespace ExecutionBreadth

open GraphQL.Execution

variable {ObjectRef : Type}

theorem slots_mapAccumList_nil (step : σ -> α -> σ × β) (state : σ)
    : mapAccumList step state [] = (state, []) := by
  rfl

theorem slots_mapAccumList_cons
    (step : σ -> α -> σ × β)
    (state : σ) (value : α) (values : List α)
    : mapAccumList step state (value :: values)
      = let head := step state value
        let tail := mapAccumList step head.fst values
        (tail.fst, head.snd :: tail.snd) := by
  rfl

theorem slots_mapAccumList_snd_eq_of_step_snd_eq
    (step : σ -> α -> σ × β)
    (hstep
      : ∀ (left right : σ) (value : α), (step left value).snd = (step right value).snd)
    : ∀ (left right : σ) (values : List α),
        (mapAccumList step left values).snd = (mapAccumList step right values).snd
  | left, right, [] => by
      simp [mapAccumList]
  | left, right, value :: values => by
      simp [mapAccumList, hstep left right value]
      exact slots_mapAccumList_snd_eq_of_step_snd_eq
        step hstep (step left value).fst (step right value).fst values

theorem slots_buildValueSlot_snd_eq
    (schema : Schema) (selectionSet : List Selection)
    (fieldType : TypeRef) (value : ResolverValue ObjectRef)
    (left right : PendingChildWorkList ObjectRef)
    : (buildValueSlot schema selectionSet fieldType value left).snd
      = (buildValueSlot schema selectionSet fieldType value right).snd := by
  induction fieldType generalizing value left right with
  | named typeName =>
      cases value with
      | null =>
          simp [buildValueSlot]
      | scalar scalarValue =>
          by_cases hcomposite : (TypeRef.named typeName).isCompositeBool schema = true
          · simp [buildValueSlot, hcomposite]
          · simp [buildValueSlot, hcomposite]
      | object runtimeType ref =>
          by_cases hincludes : schema.typeIncludesObjectBool typeName runtimeType = true
          · simp [buildValueSlot, hincludes]
          · simp [buildValueSlot, hincludes]
      | list values =>
          simp [buildValueSlot]
  | list inner ih =>
      cases value with
      | null =>
          simp [buildValueSlot]
      | scalar scalarValue =>
          simp [buildValueSlot]
      | object runtimeType ref =>
          simp [buildValueSlot]
      | list values =>
          simp [buildValueSlot]
          exact slots_mapAccumList_snd_eq_of_step_snd_eq
            (fun state value => buildValueSlot schema selectionSet inner value state)
            (fun left right value => ih value left right)
            left right values
  | nonNull inner ih =>
      simpa [buildValueSlot] using ih value left right

theorem slots_mapAccumList_buildValueSlot_snd_eq
    (schema : Schema) (selectionSet : List Selection)
    (fieldType : TypeRef) (values : List (ResolverValue ObjectRef))
    (left right : PendingChildWorkList ObjectRef)
    : (mapAccumList
        (fun state value => buildValueSlot schema selectionSet fieldType value state)
        left values).snd
      = (mapAccumList
          (fun state value => buildValueSlot schema selectionSet fieldType value state)
          right values).snd := by
  exact slots_mapAccumList_snd_eq_of_step_snd_eq
    (fun state value => buildValueSlot schema selectionSet fieldType value state)
    (fun left right value => slots_buildValueSlot_snd_eq schema selectionSet fieldType value left right)
    left right values

theorem slots_buildFieldSlotForResolved_snd_eq
    (schema : Schema) (fieldType : TypeRef) (selectionSet : List Selection)
    (resolved : Option (ResolverValue ObjectRef))
    (left right : PendingChildWorkList ObjectRef)
    : (buildFieldSlotForResolved schema fieldType selectionSet left resolved).snd
      = (buildFieldSlotForResolved schema fieldType selectionSet right resolved).snd := by
  cases resolved with
  | none =>
      simp [buildFieldSlotForResolved]
  | some value =>
      simpa [buildFieldSlotForResolved] using
        slots_buildValueSlot_snd_eq schema selectionSet fieldType value left right

theorem slots_mapAccumList_buildFieldSlotForResolved_snd_eq
    (schema : Schema) (fieldType : TypeRef) (selectionSet : List Selection)
    (resolved : List (Option (ResolverValue ObjectRef)))
    (left right : PendingChildWorkList ObjectRef)
    : (mapAccumList
        (buildFieldSlotForResolved schema fieldType selectionSet)
        left resolved).snd
      = (mapAccumList
          (buildFieldSlotForResolved schema fieldType selectionSet)
          right resolved).snd := by
  exact slots_mapAccumList_snd_eq_of_step_snd_eq
    (buildFieldSlotForResolved schema fieldType selectionSet)
    (fun left right resolved =>
      slots_buildFieldSlotForResolved_snd_eq schema fieldType selectionSet
        resolved left right)
    left right resolved

theorem slots_buildFieldSlotsForResolved_snd_eq
    (schema : Schema) (fieldType : TypeRef) (selectionSet : List Selection)
    (resolved : List (Option (ResolverValue ObjectRef)))
    (left right : PendingChildWorkList ObjectRef)
    : (buildFieldSlotsForResolved schema fieldType selectionSet resolved left).snd
      = (buildFieldSlotsForResolved schema fieldType selectionSet resolved
          right).snd := by
  simpa [buildFieldSlotsForResolved] using
    slots_mapAccumList_buildFieldSlotForResolved_snd_eq
      schema fieldType selectionSet resolved left right

theorem slots_buildFieldSlotsForResolvedSegments_snd_eq
    (schema : Schema) (fieldType : TypeRef)
    (segments
      : List (ScheduleSegment ObjectRef × List (Option (ResolverValue ObjectRef))))
    (left right : PendingChildWorkList ObjectRef)
    : (buildFieldSlotsForResolvedSegments schema fieldType segments left).snd
      = (buildFieldSlotsForResolvedSegments schema fieldType segments right).snd := by
  induction segments generalizing left right with
  | nil =>
      rfl
  | cons entry rest ih =>
      rcases entry with ⟨segment, resolved⟩
      simp [buildFieldSlotsForResolvedSegments]
      have hhead :=
        slots_buildFieldSlotsForResolved_snd_eq
          schema fieldType segment.childSelectionSet resolved left right
      have htail :=
        ih
          (buildFieldSlotsForResolved schema fieldType segment.childSelectionSet
            resolved left).fst
          (buildFieldSlotsForResolved schema fieldType segment.childSelectionSet
            resolved right).fst
      simp [hhead, htail]

theorem slots_splitResolvedBySegments_nil
    (resolved : List (Option (ResolverValue ObjectRef)))
    : splitResolvedBySegments ([] : List (ScheduleSegment ObjectRef)) resolved = [] := by
  rfl

theorem slots_splitResultsByLengths_map_length_flatten (segments : List (List α))
    : splitResultsByLengths (segments.map List.length) segments.flatten = segments := by
  induction segments with
  | nil =>
      rfl
  | cons segment segments ih =>
      simp [splitResultsByLengths, ih]

theorem slots_buildFieldSlots_nil
    (schema : Schema) (fieldType : TypeRef)
    (resolved : List (Option (ResolverValue ObjectRef)))
    : buildFieldSlots schema fieldType [] resolved = ([], []) := by
  simp [buildFieldSlots, buildFieldSlotsLoop,
    buildFieldSlotsForResolvedSegments, slots_splitResolvedBySegments_nil]

theorem slots_completeSlot_completed_preserves_stack
    (fieldType : TypeRef) (result : Result ResponseValue)
    (stack : CompletionStack)
    : (completeSlot fieldType (.completed result) stack).snd = stack := by
  induction fieldType with
  | named _typeName =>
      simp [completeSlot]
  | list inner ih =>
      simp [completeSlot]
  | nonNull inner ih =>
      simp [completeSlot, ih]

theorem slots_completeSlot_completed_error
    (fieldType : TypeRef) (errors : Nat) (stack : CompletionStack)
    : (completeSlot fieldType (.completed (.error errors)) stack).fst
      = .error errors := by
  induction fieldType with
  | named _typeName =>
      simp [completeSlot]
  | list inner ih =>
      simp [completeSlot]
  | nonNull inner ih =>
      simp [completeSlot, ih, nonNullCompletion]

theorem slots_completeSlot_completed_handleFieldError
    (fieldType : TypeRef) (stack : CompletionStack)
    : (completeSlot fieldType (.completed (handleFieldError fieldType)) stack).fst
      = handleFieldError fieldType := by
  cases fieldType with
  | named _typeName =>
      simp [handleFieldError, completeSlot]
  | list inner =>
      simp [handleFieldError, completeSlot]
  | nonNull inner =>
      simp [handleFieldError, completeSlot, nonNullCompletion,
        slots_completeSlot_completed_error]

theorem slots_completeSlot_completed_handleFieldError_full
    (fieldType : TypeRef) (stack : CompletionStack)
    : completeSlot fieldType (.completed (handleFieldError fieldType)) stack
      = (handleFieldError fieldType, stack) := by
  cases fieldType with
  | named _typeName =>
      simp [completeSlot, handleFieldError]
  | list inner =>
      simp [completeSlot, handleFieldError]
  | nonNull inner =>
      simp [completeSlot, handleFieldError, nonNullCompletion,
        slots_completeSlot_completed_error,
        slots_completeSlot_completed_preserves_stack]

theorem slots_singleFieldResultValue_singleFieldResult
    (responseName : Name) (completed : Result ResponseValue)
    : singleFieldResultValue responseName
        (GraphQL.Execution.singleFieldResult responseName completed)
      = completed := by
  cases completed with
  | error errors =>
      rfl
  | ok result =>
      cases result
      simp [singleFieldResultValue, GraphQL.Execution.singleFieldResult]

theorem slots_completeSlotList_results_length
    (fieldType : TypeRef) (slots : List ValueSlot)
    (stack : CompletionStack)
    : (completeSlotList fieldType slots stack).fst.length = slots.length := by
  induction slots generalizing stack with
  | nil =>
      simp [completeSlotList]
  | cons slot rest ih =>
      simp [completeSlotList, ih]

theorem slots_completeSlotList_completed_preserves_stack
    (fieldType : TypeRef) (results : List (Result ResponseValue))
    (stack : CompletionStack)
    : (completeSlotList fieldType (results.map ValueSlot.completed) stack).snd
      = stack := by
  induction results generalizing stack with
  | nil =>
      simp [completeSlotList]
  | cons result rest ih =>
      simp [completeSlotList, slots_completeSlot_completed_preserves_stack, ih]

theorem slots_completeSlotList_completed_results
    (fieldType : TypeRef) (results : List (Result ResponseValue))
    (stack : CompletionStack)
    : (completeSlotList fieldType (results.map ValueSlot.completed) stack).fst
      = results.map
          (fun result =>
            (completeSlot fieldType (.completed result) stack).fst) := by
  induction results generalizing stack with
  | nil =>
      simp [completeSlotList]
  | cons result rest ih =>
      simp [completeSlotList, slots_completeSlot_completed_preserves_stack, ih]

theorem slots_completeSlotList_completed
    (fieldType : TypeRef) (results : List (Result ResponseValue))
    (stack : CompletionStack)
    : completeSlotList fieldType (results.map ValueSlot.completed) stack
      = (
        results.map
          (fun result =>
            (completeSlot fieldType (.completed result) stack).fst),
        stack
      ) := by
  apply Prod.ext
  · exact slots_completeSlotList_completed_results fieldType results stack
  · exact slots_completeSlotList_completed_preserves_stack fieldType results stack

theorem slots_completeSlotList_append
    (fieldType : TypeRef) (left right : List ValueSlot)
    (stack : CompletionStack)
    : completeSlotList fieldType (left ++ right) stack
      = let completedLeft := completeSlotList fieldType left stack
        let completedRight := completeSlotList fieldType right completedLeft.snd
        (completedLeft.fst ++ completedRight.fst, completedRight.snd) := by
  induction left generalizing stack with
  | nil =>
      simp [completeSlotList]
  | cons slot left ih =>
      simp [completeSlotList, ih]

theorem slots_completeSlotList_completed_handleFieldError
    (fieldType : TypeRef) (count : Nat) (stack : CompletionStack)
    : completeSlotList fieldType
        (List.replicate count (.completed (handleFieldError fieldType))) stack
      = (List.replicate count (handleFieldError fieldType), stack) := by
  rw [← List.map_replicate]
  rw [slots_completeSlotList_completed]
  simp [slots_completeSlot_completed_handleFieldError]

theorem slots_completeSlotList_completed_error
    (fieldType : TypeRef) (errors count : Nat) (stack : CompletionStack)
    : completeSlotList fieldType (List.replicate count (.completed (.error errors))) stack
      = (List.replicate count (.error errors), stack) := by
  rw [← List.map_replicate]
  rw [slots_completeSlotList_completed]
  simp [slots_completeSlot_completed_error]

theorem catchBubbleAsNull_idempotent (wrap : α -> ResponseValue) (result : Result α)
    : catchBubbleAsNull id (catchBubbleAsNull wrap result)
      = catchBubbleAsNull wrap result := by
  cases result with
  | error _errors =>
      rfl
  | ok result =>
      cases result
      rfl

theorem catchBubbleAsNull_objectResultFromFields
    (result : Result (List (Name × ResponseValue)))
    : catchBubbleAsNull id (objectResultFromFields result)
      = catchBubbleAsNull ResponseValue.object result := by
  cases result with
  | error _errors =>
      rfl
  | ok result =>
      cases result
      rfl

theorem slots_completeSlot_named_child_of_singleton_stack
    (typeName : Name) (result : Result ResponseValue)
    : completeSlot (.named typeName) .child { valueStack := [[result]], fieldStore := [] }
      = (catchBubbleAsNull id result, { valueStack := [], fieldStore := [] }) := by
  simp [completeSlot, popValueResult, popValueResultFromSegments,
    popHeadFromSegments, popHeadFromSegment]

theorem slots_completeSlot_nonNull_named_child_of_singleton_stack
    (typeName : Name) (result : Result ResponseValue)
    : completeSlot (.nonNull (.named typeName)) .child
        { valueStack := [[result]], fieldStore := [] }
      = (
        nonNullCompletion (catchBubbleAsNull id result),
        { valueStack := [], fieldStore := [] }
      ) := by
  simp [completeSlot, slots_completeSlot_named_child_of_singleton_stack]

theorem slots_completeSlot_named_child_of_prefixed_stack
    (typeName : Name) (result : Result ResponseValue)
    (stack : CompletionStack)
    : completeSlot (.named typeName) .child
        {
          valueStack := [[result]] ++ stack.valueStack
          fieldStore := stack.fieldStore
        }
      = (
        catchBubbleAsNull id result,
        {
          valueStack := stack.valueStack
          fieldStore := stack.fieldStore
        }
      ) := by
  simp [completeSlot, popValueResult, popValueResultFromSegments,
    popHeadFromSegments, popHeadFromSegment]

theorem slots_completeSlot_nonNull_named_child_of_prefixed_stack
    (typeName : Name) (result : Result ResponseValue)
    (stack : CompletionStack)
    : completeSlot (.nonNull (.named typeName)) .child
        {
          valueStack := [[result]] ++ stack.valueStack
          fieldStore := stack.fieldStore
        }
      = (
        nonNullCompletion (catchBubbleAsNull id result),
        {
          valueStack := stack.valueStack
          fieldStore := stack.fieldStore
        }
      ) := by
  rw [completeSlot]
  rw [slots_completeSlot_named_child_of_prefixed_stack]

theorem slots_completeSlot_buildValueSlot_named_object_eq_completeValue
    (schema : Schema) (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (variableValues : VariableValues)
    (parentType runtimeType : Name) (ref : ObjectRef)
    (selectionSet : List Selection)
    (key : ScheduleKey) (fuel : Nat)
    (stack : CompletionStack)
    : schema.typeIncludesObjectBool parentType runtimeType = true
      -> completeSlot (.named parentType)
            (buildValueSlot schema selectionSet
              (.named parentType) (.object runtimeType ref) []).snd
            {
              valueStack :=
                [[expectedPendingChildWorkSpecResult schema resolvers variableValues
                    {
                      work :=
                        {
                          runtimeType := runtimeType
                          selectionSet := selectionSet
                          source := .object runtimeType ref
                        }
                      specFuel := fuel
                    }]]
                ++ stack.valueStack
              fieldStore := stack.fieldStore
            }
          = (
            GraphQL.Execution.completeValue schema resolvers variableValues
              (fuel + 1) (.named parentType)
              [key.executableField selectionSet] (.object runtimeType ref),
            stack
          ) := by
  intro hinclude
  simp [buildValueSlot, hinclude]
  have hchild :
      completeSlot (.named parentType) .child
          { valueStack :=
              [expectedPendingChildWorkSpecResult schema resolvers variableValues
                  { work :=
                      { runtimeType := runtimeType
                        selectionSet := selectionSet
                        source := .object runtimeType ref }
                    specFuel := fuel }] ::
                stack.valueStack
            fieldStore := stack.fieldStore } =
        ( catchBubbleAsNull id
            (expectedPendingChildWorkSpecResult schema resolvers variableValues
              { work :=
                  { runtimeType := runtimeType
                    selectionSet := selectionSet
                    source := .object runtimeType ref }
                specFuel := fuel })
        , stack ) := by
    simpa using
      slots_completeSlot_named_child_of_prefixed_stack
        (typeName := parentType)
        (result :=
          expectedPendingChildWorkSpecResult schema resolvers variableValues
            { work :=
                { runtimeType := runtimeType
                  selectionSet := selectionSet
                  source := .object runtimeType ref }
              specFuel := fuel })
        stack
  rw [hchild]
  simp [expectedPendingChildWorkSpecResult]
  have hcollect :
      collectFieldsByKey schema variableValues runtimeType selectionSet =
        GraphQL.Execution.collectFields schema variableValues runtimeType
          (.object runtimeType ref) selectionSet := by
    exact collectFieldsByKey_eq_collectFields_self_object schema variableValues
      runtimeType ref selectionSet
  rw [GraphQL.Execution.completeValue]
  simp [hinclude, GraphQL.Execution.collectSubfields, GraphQL.Execution.mergeExecutableGroups,
    ScheduleKey.executableField, hcollect]
  rw [catchBubbleAsNull_objectResultFromFields]

theorem slots_completeSlot_buildValueSlot_nonNull_named_object_eq_completeValue
    (schema : Schema) (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (variableValues : VariableValues)
    (parentType runtimeType : Name) (ref : ObjectRef)
    (selectionSet : List Selection)
    (key : ScheduleKey) (fuel : Nat)
    (stack : CompletionStack)
    : schema.typeIncludesObjectBool parentType runtimeType = true
      -> completeSlot (.nonNull (.named parentType))
            (buildValueSlot schema selectionSet
              (.nonNull (.named parentType)) (.object runtimeType ref) []).snd
            {
              valueStack :=
                [[expectedPendingChildWorkSpecResult schema resolvers variableValues
                    {
                      work :=
                        {
                          runtimeType := runtimeType
                          selectionSet := selectionSet
                          source := .object runtimeType ref
                        }
                      specFuel := fuel
                    }]]
                ++ stack.valueStack
              fieldStore := stack.fieldStore
            }
          = (
            GraphQL.Execution.completeValue schema resolvers variableValues
              (fuel + 1) (.nonNull (.named parentType))
              [key.executableField selectionSet] (.object runtimeType ref),
            stack
          ) := by
  intro hinclude
  rw [completeSlot]
  change
    let completed :=
      completeSlot (.named parentType)
        (buildValueSlot schema selectionSet (.named parentType) (.object runtimeType ref) []).snd
        { valueStack :=
            [[expectedPendingChildWorkSpecResult schema resolvers variableValues
                { work :=
                    { runtimeType := runtimeType
                      selectionSet := selectionSet
                      source := .object runtimeType ref }
                  specFuel := fuel }]] ++ stack.valueStack
          fieldStore := stack.fieldStore }
    (nonNullCompletion completed.fst, completed.snd) =
      ( GraphQL.Execution.completeValue schema resolvers variableValues
          (fuel + 1) (.nonNull (.named parentType))
          [key.executableField selectionSet] (.object runtimeType ref)
      , stack )
  rw [slots_completeSlot_buildValueSlot_named_object_eq_completeValue
    (ObjectRef := ObjectRef) schema resolvers variableValues
    parentType runtimeType ref selectionSet key fuel stack hinclude]
  simp [GraphQL.Execution.completeValue, hinclude, nonNullCompletion]

-----------------------------------------------------------------------------------------
-- Pending-work append structure
-----------------------------------------------------------------------------------------

theorem slots_expectedPendingChildWorkCompletionStack_append
    (schema : Schema) (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (variableValues : VariableValues)
    (left right : ExpectedPendingChildWorkList ObjectRef)
    : expectedPendingChildWorkCompletionStack schema resolvers variableValues
        (left ++ right)
      = {
        valueStack :=
          (expectedPendingChildWorkCompletionStack schema resolvers variableValues
            left).valueStack
          ++ (expectedPendingChildWorkCompletionStack schema resolvers variableValues
                right).valueStack
        fieldStore := []
      } := by
  simp [expectedPendingChildWorkCompletionStack, List.map_append]

theorem slots_expectedPendingChildWorkForCompleteValue_append
    (schema : Schema) (selectionSet : List Selection)
    (fuel : Nat) (fieldType : TypeRef)
    (value : ResolverValue ObjectRef)
    (pending : ExpectedPendingChildWorkList ObjectRef)
    : expectedPendingChildWorkForCompleteValue schema selectionSet
        fuel fieldType value pending
      = pending
        ++ expectedPendingChildWorkForCompleteValue schema selectionSet
            fuel fieldType value [] := by
  induction fieldType generalizing fuel value pending with
  | named typeName =>
      cases fuel with
      | zero =>
          simp [expectedPendingChildWorkForCompleteValue]
      | succ fuel =>
          cases value with
          | null =>
              simp [expectedPendingChildWorkForCompleteValue]
          | scalar value =>
              simp [expectedPendingChildWorkForCompleteValue]
          | object runtimeType ref =>
              by_cases hincludes :
                  schema.typeIncludesObjectBool typeName runtimeType = true
              · simp [expectedPendingChildWorkForCompleteValue, hincludes]
              · simp [expectedPendingChildWorkForCompleteValue, hincludes]
          | list values =>
              simp [expectedPendingChildWorkForCompleteValue]
  | list inner ih =>
      cases fuel with
      | zero =>
          simp [expectedPendingChildWorkForCompleteValue]
      | succ fuel =>
          cases value with
          | null =>
              simp [expectedPendingChildWorkForCompleteValue]
          | scalar value =>
              simp [expectedPendingChildWorkForCompleteValue]
          | object runtimeType ref =>
              simp [expectedPendingChildWorkForCompleteValue]
          | list values =>
              have hlistAppend :
                  ∀ (values : List (ResolverValue ObjectRef))
                    (pending : ExpectedPendingChildWorkList ObjectRef),
                    expectedPendingChildWorkForCompleteValueList schema selectionSet
                        fuel inner values pending =
                      pending ++
                        expectedPendingChildWorkForCompleteValueList schema selectionSet
                          fuel inner values [] := by
                intro values pending
                induction values generalizing pending with
                | nil =>
                    simp [expectedPendingChildWorkForCompleteValueList]
                | cons value values ihValues =>
                    have htail :
                        expectedPendingChildWorkForCompleteValueList schema selectionSet
                            fuel inner values
                            (expectedPendingChildWorkForCompleteValue
                              schema selectionSet fuel inner value pending) =
                          expectedPendingChildWorkForCompleteValue
                              schema selectionSet fuel inner value pending ++
                            expectedPendingChildWorkForCompleteValueList
                              schema selectionSet fuel inner values [] := by
                      exact ihValues
                        (expectedPendingChildWorkForCompleteValue
                          schema selectionSet fuel inner value pending)
                    rw [expectedPendingChildWorkForCompleteValueList]
                    rw [htail]
                    rw [ih fuel value pending]
                    have htail0 :=
                      ihValues
                        (expectedPendingChildWorkForCompleteValue
                          schema selectionSet fuel inner value [])
                    simpa [expectedPendingChildWorkForCompleteValueList,
                      List.append_assoc] using htail0.symm
              simpa [expectedPendingChildWorkForCompleteValue] using
                hlistAppend values pending
  | nonNull inner ih =>
      cases fuel with
      | zero =>
          simp [expectedPendingChildWorkForCompleteValue]
      | succ fuel =>
          simpa [expectedPendingChildWorkForCompleteValue] using
            (ih (fuel + 1) value pending)

theorem slots_expectedPendingChildWorkForCompleteValueList_append
    (schema : Schema) (selectionSet : List Selection)
    (fuel : Nat) (inner : TypeRef)
    (values : List (ResolverValue ObjectRef))
    (pending : ExpectedPendingChildWorkList ObjectRef)
    : expectedPendingChildWorkForCompleteValueList schema selectionSet
        fuel inner values pending
      = pending
        ++ expectedPendingChildWorkForCompleteValueList schema selectionSet
            fuel inner values [] := by
  induction values generalizing pending with
  | nil =>
      simp [expectedPendingChildWorkForCompleteValueList]
  | cons value values ih =>
      have htail :
          expectedPendingChildWorkForCompleteValueList schema selectionSet
              fuel inner values
              (expectedPendingChildWorkForCompleteValue schema selectionSet
                fuel inner value pending) =
            expectedPendingChildWorkForCompleteValue schema selectionSet
                fuel inner value pending ++
              expectedPendingChildWorkForCompleteValueList schema selectionSet
                fuel inner values [] := by
        exact ih
          (expectedPendingChildWorkForCompleteValue schema selectionSet
            fuel inner value pending)
      rw [expectedPendingChildWorkForCompleteValueList]
      rw [htail]
      rw [slots_expectedPendingChildWorkForCompleteValue_append
        schema selectionSet fuel inner value pending]
      have htail0 :=
        ih (expectedPendingChildWorkForCompleteValue schema selectionSet
          fuel inner value [])
      simpa [expectedPendingChildWorkForCompleteValueList, List.append_assoc] using
        htail0.symm

theorem slots_combineListResults_completeValueList
    (schema : Schema) (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (variableValues : VariableValues)
    (fuel : Nat) (inner : TypeRef)
    (field : ExecutableField)
    (values : List (ResolverValue ObjectRef))
    : combineListResults
        (values.map
          (fun value =>
            GraphQL.Execution.completeValue schema resolvers variableValues
              fuel inner [field] value))
      = GraphQL.Execution.completeValueList schema resolvers variableValues
          fuel inner [field] values := by
  induction values with
  | nil =>
      simp [combineListResults, GraphQL.Execution.completeValueList]
  | cons value values ih =>
      simp [combineListResults, GraphQL.Execution.completeValueList, ih]

mutual
  theorem slots_completeSlot_buildValueSlot_eq_completeValue
      (schema : Schema) (resolvers : GraphQL.Execution.Resolvers ObjectRef)
      (variableValues : VariableValues)
      (selectionSet : List Selection) (key : ScheduleKey)
      : ∀ (depth : Nat) (fieldType : TypeRef)
          (value : ResolverValue ObjectRef) (stack : CompletionStack),
          0 < depth
          -> typeRefCompleteValueFuelBound fieldType <= depth
          -> completeSlot fieldType
                (buildValueSlot schema selectionSet fieldType value []).snd
                {
                  valueStack :=
                    (expectedPendingChildWorkCompletionStack schema resolvers
                      variableValues
                      (expectedPendingChildWorkForCompleteValue schema selectionSet
                        depth fieldType value [])).valueStack
                    ++ stack.valueStack
                  fieldStore := stack.fieldStore
                }
              = (
                GraphQL.Execution.completeValue schema resolvers variableValues
                  depth fieldType [key.executableField selectionSet] value,
                stack
              )
    | 0, _fieldType, _value, _stack, hdepth, _hready => by
        cases hdepth
    | depth + 1, .named typeName, value, stack, _hdepth, _hready => by
        cases value with
        | null =>
            simp [buildValueSlot, completeSlot, expectedPendingChildWorkForCompleteValue,
              expectedPendingChildWorkCompletionStack, GraphQL.Execution.completeValue]
        | scalar scalarValue =>
            by_cases hcomposite : (TypeRef.named typeName).isCompositeBool schema = true
            · simp [buildValueSlot, completeSlot, expectedPendingChildWorkForCompleteValue,
                expectedPendingChildWorkCompletionStack, GraphQL.Execution.completeValue,
                hcomposite]
            · have hcompositeFalse :
                  (TypeRef.named typeName).isCompositeBool schema = false := by
                cases h : (TypeRef.named typeName).isCompositeBool schema with
                | false => rfl
                | true => exact False.elim (hcomposite h)
              simp [buildValueSlot, completeSlot, expectedPendingChildWorkForCompleteValue,
                expectedPendingChildWorkCompletionStack, GraphQL.Execution.completeValue,
                hcompositeFalse]
        | object runtimeType ref =>
            by_cases hincludes : schema.typeIncludesObjectBool typeName runtimeType = true
            · simpa [expectedPendingChildWorkForCompleteValue,
                expectedPendingChildWorkCompletionStack,
                expectedPendingChildWorkCompletion, hincludes] using
                slots_completeSlot_buildValueSlot_named_object_eq_completeValue
                  (ObjectRef := ObjectRef) schema resolvers variableValues
                  typeName runtimeType ref selectionSet key depth stack hincludes
            · have hincludesFalse :
                  schema.typeIncludesObjectBool typeName runtimeType = false := by
                cases h : schema.typeIncludesObjectBool typeName runtimeType with
                | false => rfl
                | true => exact False.elim (hincludes h)
              simp [buildValueSlot, completeSlot, expectedPendingChildWorkForCompleteValue,
                expectedPendingChildWorkCompletionStack, GraphQL.Execution.completeValue,
                hincludesFalse]
        | list values =>
            simp [buildValueSlot, completeSlot, expectedPendingChildWorkForCompleteValue,
              expectedPendingChildWorkCompletionStack, GraphQL.Execution.completeValue]
    | depth + 1, .list inner, value, stack, _hdepth, hready => by
        cases value with
        | null =>
            simp [buildValueSlot, completeSlot, expectedPendingChildWorkForCompleteValue,
              expectedPendingChildWorkCompletionStack, GraphQL.Execution.completeValue]
        | scalar scalarValue =>
            simp [buildValueSlot, completeSlot, expectedPendingChildWorkForCompleteValue,
              expectedPendingChildWorkCompletionStack, GraphQL.Execution.completeValue]
        | object runtimeType ref =>
            simp [buildValueSlot, completeSlot, expectedPendingChildWorkForCompleteValue,
              expectedPendingChildWorkCompletionStack, GraphQL.Execution.completeValue]
        | list values =>
            have hinnerReady : typeRefCompleteValueFuelBound inner <= depth := by
              simp [typeRefCompleteValueFuelBound] at hready
              omega
            have hcompleted :=
              slots_completeSlotList_buildValueSlots_eq_completeValueList
                schema resolvers variableValues selectionSet key
                depth inner values stack (by
                  have hpos := typeRefCompleteValueFuelBound_pos inner
                  omega) hinnerReady
            have hcombine :=
              slots_combineListResults_completeValueList
                (ObjectRef := ObjectRef) schema resolvers variableValues
                depth inner (key.executableField selectionSet) values
            calc
              completeSlot (.list inner)
                  (buildValueSlot schema selectionSet (.list inner)
                    (.list values) []).snd
                  { valueStack :=
                      (expectedPendingChildWorkCompletionStack schema resolvers
                        variableValues
                        (expectedPendingChildWorkForCompleteValue schema selectionSet
                          (depth + 1) (.list inner) (.list values) [])).valueStack ++
                        stack.valueStack
                    fieldStore := stack.fieldStore } =
                ( listResultFromItems
                    (completeSlotList inner
                      (mapAccumList
                        (fun state value => buildValueSlot schema selectionSet inner value state)
                        [] values).snd
                      { valueStack :=
                          (expectedPendingChildWorkCompletionStack schema resolvers
                            variableValues
                            (expectedPendingChildWorkForCompleteValueList schema
                              selectionSet depth inner values [])).valueStack ++
                            stack.valueStack
                        fieldStore := stack.fieldStore }).fst
                , (completeSlotList inner
                    (mapAccumList
                      (fun state value => buildValueSlot schema selectionSet inner value state)
                      [] values).snd
                    { valueStack :=
                        (expectedPendingChildWorkCompletionStack schema resolvers
                          variableValues
                          (expectedPendingChildWorkForCompleteValueList schema
                            selectionSet depth inner values [])).valueStack ++
                          stack.valueStack
                      fieldStore := stack.fieldStore }).snd ) := by
                    simp [buildValueSlot, completeSlot, expectedPendingChildWorkForCompleteValue]
              _ = (listResultFromItems
                    (values.map (fun value =>
                      GraphQL.Execution.completeValue schema resolvers variableValues
                        depth inner [key.executableField selectionSet] value)),
                    stack) := by
                      rw [hcompleted]
              _ = (GraphQL.Execution.completeValue schema resolvers variableValues
                    (depth + 1) (.list inner) [key.executableField selectionSet]
                    (.list values), stack) := by
                      simp [listResultFromItems, GraphQL.Execution.completeValue]
                      rw [hcombine]
    | depth + 1, .nonNull inner, value, stack, hdepth, hready => by
        have hrec :=
          slots_completeSlot_buildValueSlot_eq_completeValue
            schema resolvers variableValues selectionSet key
            (depth + 1) inner value stack hdepth (by
              simpa [typeRefCompleteValueFuelBound] using hready)
        simpa [buildValueSlot, completeSlot, expectedPendingChildWorkForCompleteValue,
          expectedPendingChildWorkCompletionStack, expectedPendingChildWorkCompletion,
          GraphQL.Execution.completeValue] using
          congrArg
            (fun completed => (nonNullCompletion completed.fst, completed.snd))
            hrec
  termination_by depth fieldType value _stack _hdepth _hready =>
    (depth, 0, sizeOf fieldType, sizeOf value)
  decreasing_by
    all_goals
      try subst_vars
      simp_wf
      try simp [List._sizeOf_1]
      repeat first
        | apply Prod.Lex.right
        | apply Prod.Lex.left
      omega

  theorem slots_completeSlotList_buildValueSlots_eq_completeValueList
      (schema : Schema) (resolvers : GraphQL.Execution.Resolvers ObjectRef)
      (variableValues : VariableValues)
      (selectionSet : List Selection) (key : ScheduleKey)
      : ∀ (depth : Nat) (inner : TypeRef)
          (values : List (ResolverValue ObjectRef)) (stack : CompletionStack),
          0 < depth
          -> typeRefCompleteValueFuelBound inner <= depth
          -> completeSlotList inner
                (mapAccumList
                  (fun state value =>
                    buildValueSlot schema selectionSet inner value state)
                  [] values).snd
                {
                  valueStack :=
                    (expectedPendingChildWorkCompletionStack schema resolvers
                      variableValues
                      (expectedPendingChildWorkForCompleteValueList schema
                        selectionSet depth inner values [])).valueStack
                    ++ stack.valueStack
                  fieldStore := stack.fieldStore
                }
              = (
                values.map
                  (fun value =>
                    GraphQL.Execution.completeValue schema resolvers variableValues
                      depth inner [key.executableField selectionSet] value),
                stack
              )
    | depth, inner, [], stack, _hdepth, _hready => by
        simp [mapAccumList, completeSlotList, expectedPendingChildWorkForCompleteValueList,
          expectedPendingChildWorkCompletionStack]
    | depth, inner, value :: values, stack, hdepth, hready => by
        let headWork :=
          expectedPendingChildWorkForCompleteValue schema selectionSet
            depth inner value []
        let tailWork :=
          expectedPendingChildWorkForCompleteValueList schema selectionSet
            depth inner values []
        have hwork :
            expectedPendingChildWorkForCompleteValueList schema selectionSet
                depth inner (value :: values) [] =
              headWork ++ tailWork := by
          rw [expectedPendingChildWorkForCompleteValueList]
          simp [headWork, tailWork]
          simpa [headWork, tailWork] using
            slots_expectedPendingChildWorkForCompleteValueList_append
              (ObjectRef := ObjectRef) schema selectionSet depth inner values headWork
        let tailStack : CompletionStack :=
          { valueStack :=
              (expectedPendingChildWorkCompletionStack schema resolvers
                variableValues tailWork).valueStack ++ stack.valueStack
            fieldStore := stack.fieldStore }
        let currentStack : CompletionStack :=
          { valueStack :=
              (expectedPendingChildWorkCompletionStack schema resolvers
                variableValues
                (expectedPendingChildWorkForCompleteValueList schema
                  selectionSet depth inner (value :: values) [])).valueStack ++
                stack.valueStack
            fieldStore := stack.fieldStore }
        let splitStack : CompletionStack :=
          { valueStack :=
              (expectedPendingChildWorkCompletionStack schema resolvers
                variableValues headWork).valueStack ++
                tailStack.valueStack
            fieldStore := tailStack.fieldStore }
        have hstack :
            currentStack = splitStack := by
          simp [currentStack, splitStack, tailStack, headWork, tailWork, hwork,
            slots_expectedPendingChildWorkCompletionStack_append, List.append_assoc]
        have hhead :=
          slots_completeSlot_buildValueSlot_eq_completeValue
            schema resolvers variableValues selectionSet key
            depth inner value tailStack hdepth hready
        have htail :=
          slots_completeSlotList_buildValueSlots_eq_completeValueList
            schema resolvers variableValues selectionSet key
            depth inner values stack hdepth hready
        have hslots :
            (mapAccumList
              (fun state value => buildValueSlot schema selectionSet inner value state)
              (buildValueSlot schema selectionSet inner value []).fst values).snd =
            (mapAccumList
              (fun state value => buildValueSlot schema selectionSet inner value state)
              [] values).snd := by
          exact slots_mapAccumList_buildValueSlot_snd_eq
            schema selectionSet inner values
            (buildValueSlot schema selectionSet inner value []).fst []
        change completeSlotList inner
            (mapAccumList
              (fun state value => buildValueSlot schema selectionSet inner value state)
              [] (value :: values)).snd
            currentStack =
          (List.map
            (fun value =>
              GraphQL.Execution.completeValue schema resolvers variableValues
                depth inner [key.executableField selectionSet] value)
            (value :: values), stack)
        rw [hstack]
        simp only [mapAccumList, completeSlotList]
        rw [hhead, hslots, htail]
        simp
  termination_by depth inner values _stack _hdepth _hready =>
    (depth, 1, sizeOf inner, sizeOf values)
  decreasing_by
    all_goals
      try subst_vars
      simp_wf
      try simp [List._sizeOf_1]
      repeat first
        | apply Prod.Lex.right
        | apply Prod.Lex.left
      omega
end

theorem slots_expectedPendingChildWorkForResolved_append
    (schema : Schema) (selectionSet : List Selection)
    (fieldType : TypeRef) (fuel : Nat)
    (resolved : Option (ResolverValue ObjectRef))
    (pending : ExpectedPendingChildWorkList ObjectRef)
    : expectedPendingChildWorkForResolved schema selectionSet
        fieldType fuel resolved pending
      = pending
        ++ expectedPendingChildWorkForResolved schema selectionSet
            fieldType fuel resolved [] := by
  cases fuel with
  | zero =>
      simp [expectedPendingChildWorkForResolved]
  | succ fuel =>
      cases resolved with
      | none =>
          simp [expectedPendingChildWorkForResolved]
      | some value =>
          simpa [expectedPendingChildWorkForResolved] using
            slots_expectedPendingChildWorkForCompleteValue_append
              (ObjectRef := ObjectRef) schema selectionSet
              fuel fieldType value pending

theorem slots_expectedPendingChildWorkForSources_append
    (schema : Schema) (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (fieldKey : ScheduleKey) (selectionSet : List Selection)
    (fieldType : TypeRef)
    (sources : List (ResolverValue ObjectRef))
    (specFuels : List Nat)
    (pending : ExpectedPendingChildWorkList ObjectRef)
    : expectedPendingChildWorkForSources schema resolvers fieldKey
        selectionSet fieldType sources specFuels pending
      = pending
        ++ expectedPendingChildWorkForSources schema resolvers fieldKey
            selectionSet fieldType sources specFuels [] := by
  induction sources generalizing specFuels pending with
  | nil =>
      simp [expectedPendingChildWorkForSources]
  | cons source sources ih =>
      cases specFuels with
      | nil =>
          simp [expectedPendingChildWorkForSources]
      | cons fuel specFuels =>
          rw [expectedPendingChildWorkForSources]
          rw [ih specFuels
            (expectedPendingChildWorkForResolved schema selectionSet
              fieldType fuel
              (resolvers.resolve fieldKey.parentType fieldKey.fieldName
                fieldKey.arguments source)
              pending)]
          rw [slots_expectedPendingChildWorkForResolved_append
            schema selectionSet fieldType fuel
            (resolvers.resolve fieldKey.parentType fieldKey.fieldName
              fieldKey.arguments source)
            pending]
          have htail0 :=
            ih specFuels
              (expectedPendingChildWorkForResolved schema selectionSet
                fieldType fuel
                (resolvers.resolve fieldKey.parentType fieldKey.fieldName
                  fieldKey.arguments source)
                [])
          simp [expectedPendingChildWorkForSources, List.append_assoc, htail0.symm]

theorem slots_expectedPendingChildWorkForSegment_append
    (schema : Schema) (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (fieldKey : ScheduleKey) (fieldType : TypeRef)
    (segment : ExpectedQueueSegment ObjectRef)
    (pending : ExpectedPendingChildWorkList ObjectRef)
    : expectedPendingChildWorkForSegment schema resolvers fieldKey
        fieldType segment pending
      = pending
        ++ expectedPendingChildWorkForSegment schema resolvers fieldKey
            fieldType segment [] := by
  simpa [expectedPendingChildWorkForSegment] using
    slots_expectedPendingChildWorkForSources_append
      (ObjectRef := ObjectRef) schema resolvers fieldKey
      segment.segment.childSelectionSet fieldType
      segment.segment.sources segment.specFuels pending

theorem slots_expectedPendingChildWorkForSegments_append
    (schema : Schema) (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (fieldKey : ScheduleKey) (fieldType : TypeRef)
    (segments : List (ExpectedQueueSegment ObjectRef))
    (pending : ExpectedPendingChildWorkList ObjectRef)
    : (segments.foldl
        (fun pending segment =>
          expectedPendingChildWorkForSegment schema resolvers fieldKey
            fieldType segment pending)
        pending)
      = pending
        ++ (segments.foldl
              (fun pending segment =>
                expectedPendingChildWorkForSegment schema resolvers fieldKey
                  fieldType segment pending)
              []) := by
  induction segments generalizing pending with
  | nil =>
      simp
  | cons segment segments ih =>
      simp only [List.foldl_cons]
      rw [ih
        (expectedPendingChildWorkForSegment schema resolvers fieldKey
          fieldType segment pending)]
      rw [slots_expectedPendingChildWorkForSegment_append
        schema resolvers fieldKey fieldType segment pending]
      have htail :=
        ih (expectedPendingChildWorkForSegment schema resolvers fieldKey
          fieldType segment [])
      simp [List.append_assoc, htail.symm]

-----------------------------------------------------------------------------------------
-- Field-slot completion against spec single-field results
-----------------------------------------------------------------------------------------

theorem slots_completeSlot_buildFieldSlotForResolved_eq_expectedScheduleResult
    (schema : Schema) (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (variableValues : VariableValues)
    (key : ScheduleKey) (fieldDefinition : FieldDefinition)
    (selectionSet : List Selection)
    (source : ResolverValue ObjectRef) (fuel : Nat)
    (stack : CompletionStack)
    : schema.lookupField key.parentType key.fieldName = some fieldDefinition
      -> typeRefCompleteValueFuelBound fieldDefinition.outputType < fuel
      -> completeSlot fieldDefinition.outputType
            (buildFieldSlotForResolved schema fieldDefinition.outputType selectionSet []
              (resolvers.resolve key.parentType key.fieldName key.arguments source)).snd
            {
              valueStack :=
                (expectedPendingChildWorkCompletionStack schema resolvers
                  variableValues
                  (expectedPendingChildWorkForResolved schema selectionSet
                    fieldDefinition.outputType fuel
                    (resolvers.resolve key.parentType key.fieldName key.arguments source)
                    [])).valueStack
                ++ stack.valueStack
              fieldStore := stack.fieldStore
            }
          = (
            singleFieldResultValue key.responseName
              (GraphQL.Execution.executeField schema resolvers variableValues fuel
                source key.responseName [key.executableField selectionSet]),
            stack
          ) := by
  intro hlookup hready
  cases hresolve
        : resolvers.resolve key.parentType key.fieldName key.arguments source with
  | none =>
      cases fuel with
      | zero =>
          have hpos := typeRefCompleteValueFuelBound_pos fieldDefinition.outputType
          omega
      | succ fuel =>
          simpa [buildFieldSlotForResolved, expectedPendingChildWorkForResolved,
            expectedPendingChildWorkCompletionStack, GraphQL.Execution.executeField,
            ScheduleKey.executableField, hlookup, hresolve,
            slots_singleFieldResultValue_singleFieldResult] using
            slots_completeSlot_completed_handleFieldError_full
              fieldDefinition.outputType stack
  | some value =>
      cases fuel with
      | zero =>
          have hpos := typeRefCompleteValueFuelBound_pos fieldDefinition.outputType
          omega
      | succ fuel =>
          have hfuel : typeRefCompleteValueFuelBound fieldDefinition.outputType <= fuel := by
            omega
          have hpos : 0 < fuel := by
            have hboundPos := typeRefCompleteValueFuelBound_pos fieldDefinition.outputType
            omega
          have hcomplete :=
            slots_completeSlot_buildValueSlot_eq_completeValue
              (ObjectRef := ObjectRef) schema resolvers variableValues selectionSet key
              fuel fieldDefinition.outputType value stack hpos hfuel
          simpa [buildFieldSlotForResolved, expectedPendingChildWorkForResolved,
            GraphQL.Execution.executeField, ScheduleKey.executableField,
            hlookup, hresolve, slots_singleFieldResultValue_singleFieldResult] using hcomplete

theorem
    slots_completeSlotList_buildFieldSlotsForResolved_eq_expectedScheduleSegmentSpecFieldResultsWithFuels
    (schema : Schema) (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (variableValues : VariableValues) (key : ScheduleKey)
    (fieldDefinition : FieldDefinition) (selectionSet : List Selection)
    : ∀ (sources : List (ResolverValue ObjectRef)) (specFuels : List Nat)
        (stack : CompletionStack),
        schema.lookupField key.parentType key.fieldName = some fieldDefinition
        -> specFuels.length = sources.length
        -> (∀ fuel,
              fuel ∈ specFuels
              -> typeRefCompleteValueFuelBound fieldDefinition.outputType < fuel)
        -> completeSlotList fieldDefinition.outputType
              (buildFieldSlotsForResolved schema fieldDefinition.outputType selectionSet
                (sources.map
                  (fun source =>
                    resolvers.resolve key.parentType key.fieldName key.arguments source))
                []).snd
              {
                valueStack :=
                  (expectedPendingChildWorkCompletionStack schema resolvers
                    variableValues
                    (expectedPendingChildWorkForSources schema resolvers key selectionSet
                      fieldDefinition.outputType sources specFuels [])).valueStack
                  ++ stack.valueStack
                fieldStore := stack.fieldStore
              }
            = (
              expectedScheduleSegmentSpecFieldResultsWithFuels schema resolvers
                variableValues key selectionSet sources specFuels,
              stack
            ) := by
  intro sources
  induction sources with
  | nil =>
      intro specFuels stack hlookup hlength hready
      cases specFuels with
      | nil =>
          simp [buildFieldSlotsForResolved, mapAccumList, expectedPendingChildWorkForSources,
            expectedScheduleSegmentSpecFieldResultsWithFuels,
            expectedPendingChildWorkCompletionStack, completeSlotList]
      | cons fuel specFuels =>
          simp at hlength
  | cons source sources ih =>
      intro specFuels stack hlookup hlength hready
      cases specFuels with
      | nil =>
          simp at hlength
      | cons fuel specFuels =>
          have htailLength : specFuels.length = sources.length := by
            simpa using Nat.succ.inj hlength
          have hfuelReady :
              typeRefCompleteValueFuelBound fieldDefinition.outputType < fuel :=
            hready fuel (by simp)
          have htailReady :
              ∀ tailFuel, tailFuel ∈ specFuels ->
                typeRefCompleteValueFuelBound fieldDefinition.outputType < tailFuel := by
            intro tailFuel htailFuel
            exact hready tailFuel (by simp [htailFuel])
          let headWork :=
            expectedPendingChildWorkForResolved schema selectionSet
              fieldDefinition.outputType fuel
              (resolvers.resolve key.parentType key.fieldName
                key.arguments source) []
          let tailWork :=
            expectedPendingChildWorkForSources schema resolvers key
              selectionSet fieldDefinition.outputType sources specFuels []
          have hwork :
              expectedPendingChildWorkForSources schema resolvers key
                  selectionSet fieldDefinition.outputType
                  (source :: sources) (fuel :: specFuels) [] =
                headWork ++ tailWork := by
            rw [expectedPendingChildWorkForSources]
            simp [headWork, tailWork]
            simpa [headWork, tailWork] using
              slots_expectedPendingChildWorkForSources_append
                (ObjectRef := ObjectRef) schema resolvers key selectionSet
                fieldDefinition.outputType sources specFuels headWork
          let tailStack : CompletionStack :=
            { valueStack :=
                (expectedPendingChildWorkCompletionStack schema resolvers
                  variableValues tailWork).valueStack ++ stack.valueStack
              fieldStore := stack.fieldStore }
          let currentStack : CompletionStack :=
            { valueStack :=
                (expectedPendingChildWorkCompletionStack schema resolvers
                  variableValues
                  (expectedPendingChildWorkForSources schema resolvers key
                    selectionSet fieldDefinition.outputType
                    (source :: sources) (fuel :: specFuels) [])).valueStack ++
                  stack.valueStack
              fieldStore := stack.fieldStore }
          let splitStack : CompletionStack :=
            { valueStack :=
                (expectedPendingChildWorkCompletionStack schema resolvers
                  variableValues headWork).valueStack ++
                  tailStack.valueStack
              fieldStore := tailStack.fieldStore }
          have hstack :
              currentStack = splitStack := by
            simp [currentStack, splitStack, tailStack, headWork, tailWork, hwork,
              slots_expectedPendingChildWorkCompletionStack_append, List.append_assoc]
          have hhead :=
            slots_completeSlot_buildFieldSlotForResolved_eq_expectedScheduleResult
              (ObjectRef := ObjectRef) schema resolvers variableValues key
              fieldDefinition selectionSet source fuel tailStack hlookup hfuelReady
          have htail :=
            ih specFuels stack hlookup htailLength htailReady
          have htail' :
              completeSlotList fieldDefinition.outputType
                  (mapAccumList
                    (buildFieldSlotForResolved schema fieldDefinition.outputType selectionSet)
                    []
                    (sources.map (fun source =>
                      resolvers.resolve key.parentType key.fieldName
                        key.arguments source))).snd
                  tailStack =
                ( expectedScheduleSegmentSpecFieldResultsWithFuels schema resolvers
                    variableValues key selectionSet sources specFuels
                , stack ) := by
            simpa [buildFieldSlotsForResolved, tailStack] using htail
          have hslots :
              (mapAccumList
                (buildFieldSlotForResolved schema fieldDefinition.outputType selectionSet)
                (buildFieldSlotForResolved schema fieldDefinition.outputType
                  selectionSet []
                  (resolvers.resolve key.parentType key.fieldName
                    key.arguments source)).fst
                (sources.map (fun source =>
                  resolvers.resolve key.parentType key.fieldName
                    key.arguments source))).snd =
              (mapAccumList
                (buildFieldSlotForResolved schema fieldDefinition.outputType selectionSet)
                []
                (sources.map (fun source =>
                  resolvers.resolve key.parentType key.fieldName
                    key.arguments source))).snd := by
            exact slots_mapAccumList_buildFieldSlotForResolved_snd_eq
              schema fieldDefinition.outputType selectionSet
              (sources.map (fun source =>
                resolvers.resolve key.parentType key.fieldName
                  key.arguments source))
              (buildFieldSlotForResolved schema fieldDefinition.outputType
                selectionSet []
                (resolvers.resolve key.parentType key.fieldName
                  key.arguments source)).fst
              []
          change completeSlotList fieldDefinition.outputType
              (mapAccumList
                (buildFieldSlotForResolved schema fieldDefinition.outputType selectionSet)
                []
                (resolvers.resolve key.parentType key.fieldName key.arguments source ::
                  sources.map (fun source =>
                    resolvers.resolve key.parentType key.fieldName
                      key.arguments source))).snd
              currentStack =
            ( expectedScheduleSegmentSpecFieldResultsWithFuels schema resolvers
                variableValues key selectionSet (source :: sources) (fuel :: specFuels)
            , stack )
          rw [hstack]
          rw [slots_mapAccumList_cons
            (step := buildFieldSlotForResolved schema fieldDefinition.outputType selectionSet)
            (state := [])
            (value := resolvers.resolve key.parentType key.fieldName key.arguments source)
            (values := sources.map (fun source =>
              resolvers.resolve key.parentType key.fieldName
                key.arguments source))]
          simp [completeSlotList]
          rw [hhead, hslots]
          constructor
          · have htailF := congrArg Prod.fst htail'
            simpa [expectedScheduleSegmentSpecFieldResultsWithFuels] using
              congrArg
                (fun tail =>
                  singleFieldResultValue key.responseName
                    (GraphQL.Execution.executeField schema resolvers variableValues fuel
                      source key.responseName [key.executableField selectionSet]) ::
                    tail)
                htailF
          · exact congrArg Prod.snd htail'

theorem
    slots_completeSlotList_buildFieldSlotsForSegment_eq_expectedScheduleSegmentSpecFieldResults
    (schema : Schema) (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (variableValues : VariableValues) (key : ScheduleKey)
    (fieldDefinition : FieldDefinition) (segment : ExpectedQueueSegment ObjectRef)
    (stack : CompletionStack)
    : schema.lookupField key.parentType key.fieldName = some fieldDefinition
      -> expectedQueueSegmentFuelsAligned segment
      -> (∀ fuel,
            fuel ∈ segment.specFuels
            -> typeRefCompleteValueFuelBound fieldDefinition.outputType < fuel)
      -> completeSlotList fieldDefinition.outputType
            (buildFieldSlotsForResolved schema fieldDefinition.outputType
              segment.segment.childSelectionSet
              (segment.segment.sources.map
                (fun source =>
                  resolvers.resolve key.parentType key.fieldName key.arguments source))
              []).snd
            {
              valueStack :=
                (expectedPendingChildWorkCompletionStack schema resolvers
                  variableValues
                  (expectedPendingChildWorkForSegment schema resolvers key
                    fieldDefinition.outputType segment [])).valueStack
                ++ stack.valueStack
              fieldStore := stack.fieldStore
            }
          = (
            expectedScheduleSegmentSpecFieldResults schema resolvers variableValues
              key segment,
            stack
          ) := by
  intro hlookup haligned hready
  simpa [expectedScheduleSegmentSpecFieldResults, expectedPendingChildWorkForSegment] using
    slots_completeSlotList_buildFieldSlotsForResolved_eq_expectedScheduleSegmentSpecFieldResultsWithFuels
      (ObjectRef := ObjectRef) schema resolvers variableValues key fieldDefinition
      segment.segment.childSelectionSet segment.segment.sources segment.specFuels
      stack hlookup
      (by simpa [expectedQueueSegmentFuelsAligned] using haligned)
      hready

theorem
    slots_completeSlotList_buildFieldSlotsForResolvedSegments_eq_expectedScheduleSegmentResultsFlatten
    (schema : Schema) (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (variableValues : VariableValues) (key : ScheduleKey)
    (fieldDefinition : FieldDefinition)
    : ∀ (segments : List (ExpectedQueueSegment ObjectRef)) (stack : CompletionStack),
        schema.lookupField key.parentType key.fieldName = some fieldDefinition
        -> (∀ segment, segment ∈ segments -> expectedQueueSegmentFuelsAligned segment)
        -> (∀ segment,
              segment ∈ segments
              -> ∀ fuel,
                  fuel ∈ segment.specFuels
                  -> typeRefCompleteValueFuelBound fieldDefinition.outputType < fuel)
        -> completeSlotList fieldDefinition.outputType
              (buildFieldSlotsForResolvedSegments schema fieldDefinition.outputType
                (segments.map
                  (fun segment =>
                    (
                      segment.segment,
                      segment.segment.sources.map
                        (fun source =>
                          resolvers.resolve key.parentType key.fieldName
                            key.arguments source)
                    )))
                []).snd
              {
                valueStack :=
                  (expectedPendingChildWorkCompletionStack schema resolvers
                    variableValues
                    (segments.foldl
                      (fun pending segment =>
                        expectedPendingChildWorkForSegment schema resolvers key
                          fieldDefinition.outputType segment pending)
                      [])).valueStack
                  ++ stack.valueStack
                fieldStore := stack.fieldStore
              }
            = (
              (segments.map
                (expectedScheduleSegmentSpecFieldResults schema resolvers
                  variableValues key)).flatten,
              stack
            ) := by
  intro segments
  induction segments with
  | nil =>
      intro stack hlookup haligned hready
      simp [buildFieldSlotsForResolvedSegments, completeSlotList,
        expectedPendingChildWorkCompletionStack]
  | cons segment segments ih =>
      intro stack hlookup haligned hready
      let headWork :=
        expectedPendingChildWorkForSegment schema resolvers key
          fieldDefinition.outputType segment []
      let tailWork :=
        segments.foldl
          (fun pending segment =>
            expectedPendingChildWorkForSegment schema resolvers key
              fieldDefinition.outputType segment pending)
          []
      have hwork :
          (List.foldl
            (fun pending segment =>
              expectedPendingChildWorkForSegment schema resolvers key
                fieldDefinition.outputType segment pending)
            []
            (segment :: segments)) =
          headWork ++ tailWork := by
        rw [List.foldl_cons]
        simpa [headWork, tailWork] using
          slots_expectedPendingChildWorkForSegments_append
            (ObjectRef := ObjectRef) schema resolvers key
            fieldDefinition.outputType segments headWork
      let tailStack : CompletionStack :=
        { valueStack :=
            (expectedPendingChildWorkCompletionStack schema resolvers
              variableValues tailWork).valueStack ++ stack.valueStack
          fieldStore := stack.fieldStore }
      let currentStack : CompletionStack :=
        { valueStack :=
            (expectedPendingChildWorkCompletionStack schema resolvers
              variableValues
              ((segment :: segments).foldl
                (fun pending segment =>
                  expectedPendingChildWorkForSegment schema resolvers key
                    fieldDefinition.outputType segment pending)
                [])).valueStack ++
              stack.valueStack
          fieldStore := stack.fieldStore }
      let splitStack : CompletionStack :=
        { valueStack :=
            (expectedPendingChildWorkCompletionStack schema resolvers
              variableValues headWork).valueStack ++
              tailStack.valueStack
          fieldStore := tailStack.fieldStore }
      have hstack :
          currentStack = splitStack := by
        simp [currentStack, splitStack, tailStack, headWork, tailWork, hwork,
          slots_expectedPendingChildWorkCompletionStack_append, List.append_assoc]
      have hhead :=
        slots_completeSlotList_buildFieldSlotsForSegment_eq_expectedScheduleSegmentSpecFieldResults
          (ObjectRef := ObjectRef) schema resolvers variableValues key
          fieldDefinition segment tailStack hlookup
          (haligned segment (by simp))
          (hready segment (by simp))
      have htailAligned :
          ∀ restSegment, restSegment ∈ segments ->
            expectedQueueSegmentFuelsAligned restSegment := by
        intro restSegment hrestSegment
        exact haligned restSegment (by simp [hrestSegment])
      have htailReady :
          ∀ restSegment, restSegment ∈ segments ->
            ∀ fuel, fuel ∈ restSegment.specFuels ->
              typeRefCompleteValueFuelBound fieldDefinition.outputType < fuel := by
        intro restSegment hrestSegment fuel hfuel
        exact hready restSegment (by simp [hrestSegment]) fuel hfuel
      have htail :=
        ih stack hlookup htailAligned htailReady
      have htail' :
          completeSlotList fieldDefinition.outputType
              (buildFieldSlotsForResolvedSegments schema fieldDefinition.outputType
                (segments.map (fun segment =>
                  ( segment.segment
                  , segment.segment.sources.map (fun source =>
                      resolvers.resolve key.parentType key.fieldName
                        key.arguments source) )))
                []).snd
              tailStack =
            ( (segments.map
                  (expectedScheduleSegmentSpecFieldResults schema resolvers
                    variableValues key)).flatten
            , stack ) := by
        simpa [tailStack] using htail
      have hslots :
          (buildFieldSlotsForResolvedSegments schema fieldDefinition.outputType
            (segments.map (fun segment =>
              ( segment.segment
              , segment.segment.sources.map (fun source =>
                  resolvers.resolve key.parentType key.fieldName
                    key.arguments source) )))
            (buildFieldSlotsForResolved schema fieldDefinition.outputType
              segment.segment.childSelectionSet
              (segment.segment.sources.map (fun source =>
                resolvers.resolve key.parentType key.fieldName
                  key.arguments source))
              []).fst).snd =
          (buildFieldSlotsForResolvedSegments schema fieldDefinition.outputType
            (segments.map (fun segment =>
              ( segment.segment
              , segment.segment.sources.map (fun source =>
                  resolvers.resolve key.parentType key.fieldName
                    key.arguments source) )))
            []).snd := by
        exact slots_buildFieldSlotsForResolvedSegments_snd_eq
          schema fieldDefinition.outputType
          (segments.map (fun segment =>
            ( segment.segment
            , segment.segment.sources.map (fun source =>
                resolvers.resolve key.parentType key.fieldName
                  key.arguments source) )))
          (buildFieldSlotsForResolved schema fieldDefinition.outputType
            segment.segment.childSelectionSet
            (segment.segment.sources.map (fun source =>
              resolvers.resolve key.parentType key.fieldName
                key.arguments source))
            []).fst
          []
      change completeSlotList fieldDefinition.outputType
          (buildFieldSlotsForResolvedSegments schema fieldDefinition.outputType
            (((segment :: segments).map (fun segment =>
              ( segment.segment
              , segment.segment.sources.map (fun source =>
                  resolvers.resolve key.parentType key.fieldName
                    key.arguments source) ))))
            []).snd
          currentStack =
        ( (((segment :: segments).map
              (expectedScheduleSegmentSpecFieldResults schema resolvers
                variableValues key)).flatten)
        , stack )
      rw [hstack]
      simp [buildFieldSlotsForResolvedSegments, slots_completeSlotList_append]
      rw [hhead, hslots, htail']
      simp

-----------------------------------------------------------------------------------------
-- Pending-work accumulation shape
-----------------------------------------------------------------------------------------

theorem slots_expectedPendingChildWorkForCompleteValue_toPending_eq_buildValueSlot
    (schema : Schema) (selectionSet : List Selection)
    (fuel : Nat) (fieldType : TypeRef)
    (value : ResolverValue ObjectRef)
    (pending : ExpectedPendingChildWorkList ObjectRef)
    : typeRefCompleteValueFuelBound fieldType <= fuel
      -> expectedPendingChildWorkToPending
            (expectedPendingChildWorkForCompleteValue schema selectionSet
              fuel fieldType value pending)
          = (buildValueSlot schema selectionSet fieldType value
              (expectedPendingChildWorkToPending pending)).fst := by
  induction fieldType generalizing fuel value pending with
  | named typeName =>
      intro hfuel
      cases fuel with
      | zero =>
          simp [typeRefCompleteValueFuelBound] at hfuel
      | succ fuel =>
          cases value with
          | null =>
              simp [expectedPendingChildWorkForCompleteValue, buildValueSlot,
                expectedPendingChildWorkToPending]
          | scalar value =>
              by_cases hcomposite :
                  (TypeRef.named typeName).isCompositeBool schema = true
              · simp [expectedPendingChildWorkForCompleteValue, buildValueSlot,
                  expectedPendingChildWorkToPending, hcomposite]
              · have hcompositeFalse :
                    (TypeRef.named typeName).isCompositeBool schema = false := by
                  cases h : (TypeRef.named typeName).isCompositeBool schema with
                  | false => rfl
                  | true => exact False.elim (hcomposite h)
                simp [expectedPendingChildWorkForCompleteValue, buildValueSlot,
                  expectedPendingChildWorkToPending, hcompositeFalse]
          | object runtimeType ref =>
              by_cases hincludes :
                  schema.typeIncludesObjectBool typeName runtimeType = true
              · simp [expectedPendingChildWorkForCompleteValue, buildValueSlot,
                  expectedPendingChildWorkToPending, hincludes]
              · have hincludesFalse :
                    schema.typeIncludesObjectBool typeName runtimeType = false := by
                  cases h : schema.typeIncludesObjectBool typeName runtimeType with
                  | false => rfl
                  | true => exact False.elim (hincludes h)
                simp [expectedPendingChildWorkForCompleteValue, buildValueSlot,
                  expectedPendingChildWorkToPending, hincludesFalse]
          | list values =>
              simp [expectedPendingChildWorkForCompleteValue, buildValueSlot,
                expectedPendingChildWorkToPending]
  | list inner ih =>
      intro hfuel
      cases fuel with
      | zero =>
          simp [typeRefCompleteValueFuelBound] at hfuel
      | succ fuel =>
          have hinner : typeRefCompleteValueFuelBound inner <= fuel := by
            simp [typeRefCompleteValueFuelBound] at hfuel
            omega
          cases value with
          | null =>
              simp [expectedPendingChildWorkForCompleteValue, buildValueSlot,
                expectedPendingChildWorkToPending]
          | scalar value =>
              simp [expectedPendingChildWorkForCompleteValue, buildValueSlot,
                expectedPendingChildWorkToPending]
          | object runtimeType ref =>
              simp [expectedPendingChildWorkForCompleteValue, buildValueSlot,
                expectedPendingChildWorkToPending]
          | list values =>
              induction values generalizing pending with
              | nil =>
                  simp [expectedPendingChildWorkForCompleteValue,
                    expectedPendingChildWorkForCompleteValueList,
                    buildValueSlot, mapAccumList, expectedPendingChildWorkToPending]
              | cons value values ihValues =>
                  have hhead :=
                    ih fuel value pending hinner
                  have htail :=
                    ihValues
                      (expectedPendingChildWorkForCompleteValue schema selectionSet
                        fuel inner value pending)
                  rw [hhead] at htail
                  simpa [expectedPendingChildWorkForCompleteValue,
                    expectedPendingChildWorkForCompleteValueList,
                    buildValueSlot, mapAccumList, expectedPendingChildWorkToPending]
                    using htail
  | nonNull inner ih =>
      intro hfuel
      cases fuel with
      | zero =>
          have hpos := typeRefCompleteValueFuelBound_pos inner
          simp [typeRefCompleteValueFuelBound] at hfuel
          omega
      | succ fuel =>
          simpa [expectedPendingChildWorkForCompleteValue, buildValueSlot,
            typeRefCompleteValueFuelBound] using
            ih (fuel + 1) value pending (by
              simpa [typeRefCompleteValueFuelBound] using hfuel)

theorem slots_expectedPendingChildWorkForResolved_toPending_eq_buildFieldSlotForResolved
    (schema : Schema) (selectionSet : List Selection) (fieldType : TypeRef)
    (fuel : Nat) (resolved : Option (ResolverValue ObjectRef))
    (pending : ExpectedPendingChildWorkList ObjectRef)
    : typeRefCompleteValueFuelBound fieldType < fuel
      -> expectedPendingChildWorkToPending
            (expectedPendingChildWorkForResolved schema selectionSet
              fieldType fuel resolved pending)
          = (buildFieldSlotForResolved schema fieldType selectionSet
              (expectedPendingChildWorkToPending pending) resolved).fst := by
  intro hfuel
  cases fuel with
  | zero =>
      omega
  | succ fuel =>
      cases resolved with
      | none =>
          simp [expectedPendingChildWorkForResolved, buildFieldSlotForResolved,
            expectedPendingChildWorkToPending]
      | some value =>
          have hready : typeRefCompleteValueFuelBound fieldType <= fuel := by
            omega
          simpa [expectedPendingChildWorkForResolved, buildFieldSlotForResolved] using
            slots_expectedPendingChildWorkForCompleteValue_toPending_eq_buildValueSlot
              (ObjectRef := ObjectRef) schema selectionSet fuel fieldType value pending
              hready

theorem slots_expectedPendingChildWorkForSources_toPending_eq_buildFieldSlotsForResolved
    (schema : Schema) (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (fieldKey : ScheduleKey) (selectionSet : List Selection)
    (fieldType : TypeRef)
    (sources : List (ResolverValue ObjectRef)) (specFuels : List Nat)
    (pending : ExpectedPendingChildWorkList ObjectRef)
    : specFuels.length = sources.length
      -> (∀ fuel, fuel ∈ specFuels -> typeRefCompleteValueFuelBound fieldType < fuel)
      -> expectedPendingChildWorkToPending
            (expectedPendingChildWorkForSources schema resolvers fieldKey
              selectionSet fieldType sources specFuels pending)
          = (buildFieldSlotsForResolved schema fieldType selectionSet
              (sources.map
                (fun source =>
                  resolvers.resolve fieldKey.parentType fieldKey.fieldName
                    fieldKey.arguments source))
              (expectedPendingChildWorkToPending pending)).fst := by
  intro hlength hready
  induction sources generalizing specFuels pending with
  | nil =>
      simp [expectedPendingChildWorkForSources, buildFieldSlotsForResolved, mapAccumList]
  | cons source sources ih =>
      cases specFuels with
      | nil =>
          simp at hlength
      | cons fuel specFuels =>
          have htailLength : specFuels.length = sources.length := by
            simpa using Nat.succ.inj hlength
          have hfuelReady :
              typeRefCompleteValueFuelBound fieldType < fuel :=
            hready fuel (by simp)
          have htailReady :
              ∀ tailFuel, tailFuel ∈ specFuels ->
                typeRefCompleteValueFuelBound fieldType < tailFuel := by
            intro tailFuel htailFuel
            exact hready tailFuel (by simp [htailFuel])
          cases hresolved
                : resolvers.resolve fieldKey.parentType fieldKey.fieldName
                    fieldKey.arguments source with
          | none =>
              cases fuel with
              | zero =>
                  have hpos := typeRefCompleteValueFuelBound_pos fieldType
                  omega
              | succ fuel' =>
                  have htail :=
                    ih specFuels pending htailLength htailReady
                  simp [expectedPendingChildWorkForSources,
                    expectedPendingChildWorkForResolved, buildFieldSlotsForResolved,
                    buildFieldSlotForResolved, mapAccumList, hresolved]
                  exact htail
          | some value =>
              cases fuel with
              | zero =>
                  have hpos := typeRefCompleteValueFuelBound_pos fieldType
                  omega
              | succ fuel' =>
                  have hhead :=
                    slots_expectedPendingChildWorkForResolved_toPending_eq_buildFieldSlotForResolved
                      (ObjectRef := ObjectRef) schema selectionSet fieldType
                      (fuel' + 1) (.some value) pending (by simpa using hfuelReady)
                  have htail :=
                    ih specFuels
                      (expectedPendingChildWorkForResolved schema selectionSet
                        fieldType (fuel' + 1) (.some value) pending)
                      htailLength htailReady
                  rw [hhead] at htail
                  simp [expectedPendingChildWorkForSources,
                    expectedPendingChildWorkForResolved, buildFieldSlotsForResolved,
                    mapAccumList, hresolved] at htail ⊢
                  exact htail

theorem slots_expectedPendingChildWorkForSegment_toPending_eq_buildFieldSlotsForResolved
    (schema : Schema) (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (fieldKey : ScheduleKey) (fieldType : TypeRef)
    (segment : ExpectedQueueSegment ObjectRef)
    (pending : ExpectedPendingChildWorkList ObjectRef)
    : expectedQueueSegmentFuelsAligned segment
      -> (∀ fuel,
            fuel ∈ segment.specFuels -> typeRefCompleteValueFuelBound fieldType < fuel)
      -> expectedPendingChildWorkToPending
            (expectedPendingChildWorkForSegment schema resolvers fieldKey
              fieldType segment pending)
          = (buildFieldSlotsForResolved schema fieldType
              segment.segment.childSelectionSet
              (segment.segment.sources.map
                (fun source =>
                  resolvers.resolve fieldKey.parentType fieldKey.fieldName
                    fieldKey.arguments source))
              (expectedPendingChildWorkToPending pending)).fst := by
  intro haligned hready
  simpa [expectedPendingChildWorkForSegment] using
    slots_expectedPendingChildWorkForSources_toPending_eq_buildFieldSlotsForResolved
      (ObjectRef := ObjectRef) schema resolvers fieldKey
      segment.segment.childSelectionSet fieldType segment.segment.sources
      segment.specFuels pending
      (by simpa [expectedQueueSegmentFuelsAligned] using haligned)
      hready

theorem slots_splitResolvedBySegments_map_sources
    (segments : List (ExpectedQueueSegment ObjectRef))
    (resolve : ResolverValue ObjectRef -> Option (ResolverValue ObjectRef))
    : splitResolvedBySegments
        (segments.map ExpectedQueueSegment.segment)
        (((segments.map (fun segment => segment.segment.sources)).flatten).map resolve)
      = segments.map
          (fun segment =>
            (segment.segment, segment.segment.sources.map resolve)) := by
  induction segments with
  | nil =>
      rfl
  | cons segment rest ih =>
      let headResolved := segment.segment.sources.map resolve
      let tailSources := (rest.map (fun segment => segment.segment.sources)).flatten
      have hflatten :
          (((segment :: rest).map (fun segment => segment.segment.sources)).flatten).map
              resolve =
            headResolved ++ (tailSources.map resolve) := by
        simp [headResolved, tailSources, List.map_flatten]
      have htake :
          List.take segment.segment.sources.length
              ((((segment :: rest).map
                    (fun segment => segment.segment.sources)).flatten).map resolve) =
            headResolved := by
        rw [hflatten]
        simp [headResolved]
      have hdrop :
          List.drop segment.segment.sources.length
              ((((segment :: rest).map
                    (fun segment => segment.segment.sources)).flatten).map resolve) =
            tailSources.map resolve := by
        rw [hflatten]
        simp [headResolved]
      change (
                  segment.segment,
                  List.take segment.segment.sources.length
                    ((((segment :: rest).map
                        (fun segment => segment.segment.sources)).flatten).map
                      resolve)
                )
                :: splitResolvedBySegments (List.map ExpectedQueueSegment.segment rest)
                    (List.drop segment.segment.sources.length
                      ((((segment :: rest).map
                          (fun segment => segment.segment.sources)).flatten).map
                        resolve))
              = (segment.segment, List.map resolve segment.segment.sources)
                :: List.map
                    (fun segment =>
                      (segment.segment, List.map resolve segment.segment.sources))
                    rest
      rw [htake, hdrop]
      simpa [headResolved, tailSources, List.map_flatten] using ih

theorem slots_completeSlotList_buildFieldSlots_eq_expectedScheduleSegmentResultsFlatten
    (schema : Schema) (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (variableValues : VariableValues)
    (key : ScheduleKey) (fieldDefinition : FieldDefinition)
    (item : ExpectedQueueItem ObjectRef)
    (stack : CompletionStack)
    : schema.lookupField key.parentType key.fieldName = some fieldDefinition
      -> item.key = key
      -> expectedQueueItemFuelsAligned item
      -> (∀ segment,
            segment ∈ item.segments
            -> ∀ fuel,
                fuel ∈ segment.specFuels
                -> typeRefCompleteValueFuelBound fieldDefinition.outputType < fuel)
      -> completeSlotList fieldDefinition.outputType
            (buildFieldSlots schema fieldDefinition.outputType
              item.toScheduleItem.segments
              (item.toScheduleItem.sources.map
                (fun source =>
                  resolvers.resolve key.parentType key.fieldName
                    key.arguments source))).snd
            {
              valueStack :=
                (expectedPendingChildWorkCompletionStack schema resolvers
                  variableValues
                  (expectedPendingChildWorkForItem schema resolvers
                    fieldDefinition.outputType item)).valueStack
                ++ stack.valueStack
              fieldStore := stack.fieldStore
            }
          = (
            (item.segments.map
              (expectedScheduleSegmentSpecFieldResults schema resolvers
                variableValues key)).flatten,
            stack
          ) := by
  intro hlookup hkey haligned hready
  subst hkey
  have hsplit :
      splitResolvedBySegments item.toScheduleItem.segments
          (item.toScheduleItem.sources.map (fun source =>
            resolvers.resolve item.key.parentType item.key.fieldName
              item.key.arguments source)) =
        item.segments.map (fun segment =>
          ( segment.segment
          , segment.segment.sources.map (fun source =>
              resolvers.resolve item.key.parentType item.key.fieldName
                item.key.arguments source) )) := by
    unfold ExpectedQueueItem.toScheduleItem ScheduleItem.sources
    rw [List.map_flatten]
    simpa [Function.comp_def] using
      slots_splitResolvedBySegments_map_sources
        (ObjectRef := ObjectRef) item.segments
        (fun source =>
          resolvers.resolve item.key.parentType item.key.fieldName
            item.key.arguments source)
  simpa [buildFieldSlots, buildFieldSlotsLoop,
    expectedPendingChildWorkForItem, hsplit] using
    slots_completeSlotList_buildFieldSlotsForResolvedSegments_eq_expectedScheduleSegmentResultsFlatten
      (ObjectRef := ObjectRef) schema resolvers variableValues item.key
      fieldDefinition item.segments stack hlookup haligned hready

theorem
    slots_expectedPendingChildWorkForSegments_toPending_eq_buildFieldSlotsForResolvedSegments
    (schema : Schema) (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (fieldKey : ScheduleKey) (fieldType : TypeRef)
    (segments : List (ExpectedQueueSegment ObjectRef))
    (pending : ExpectedPendingChildWorkList ObjectRef)
    : (∀ segment, segment ∈ segments -> expectedQueueSegmentFuelsAligned segment)
      -> (∀ segment,
            segment ∈ segments
            -> ∀ fuel,
                fuel ∈ segment.specFuels
                -> typeRefCompleteValueFuelBound fieldType < fuel)
      -> expectedPendingChildWorkToPending
            (segments.foldl
              (fun pending segment =>
                expectedPendingChildWorkForSegment schema resolvers fieldKey
                  fieldType segment pending)
              pending)
          = (buildFieldSlotsForResolvedSegments schema fieldType
              (segments.map
                (fun segment =>
                  (
                    segment.segment,
                    segment.segment.sources.map
                      (fun source =>
                        resolvers.resolve fieldKey.parentType fieldKey.fieldName
                          fieldKey.arguments source)
                  )))
              (expectedPendingChildWorkToPending pending)).fst := by
  intro haligned hready
  induction segments generalizing pending with
  | nil =>
      simp [buildFieldSlotsForResolvedSegments]
  | cons segment rest ih =>
      have hhead :=
        slots_expectedPendingChildWorkForSegment_toPending_eq_buildFieldSlotsForResolved
          (ObjectRef := ObjectRef) schema resolvers fieldKey fieldType
          segment pending
          (haligned segment (by simp))
          (hready segment (by simp))
      have htailAligned :
          ∀ restSegment, restSegment ∈ rest ->
            expectedQueueSegmentFuelsAligned restSegment := by
        intro restSegment hrestSegment
        exact haligned restSegment (by simp [hrestSegment])
      have htailReady :
          ∀ restSegment, restSegment ∈ rest ->
            ∀ fuel, fuel ∈ restSegment.specFuels ->
              typeRefCompleteValueFuelBound fieldType < fuel := by
        intro restSegment hrestSegment fuel hfuel
        exact hready restSegment (by simp [hrestSegment]) fuel hfuel
      have htail :=
        ih
          (expectedPendingChildWorkForSegment schema resolvers fieldKey
            fieldType segment pending)
          htailAligned htailReady
      rw [hhead] at htail
      simp [buildFieldSlotsForResolvedSegments] at htail ⊢
      exact htail

theorem slots_expectedPendingChildWorkForItem_toPending_eq_buildFieldSlots
    (schema : Schema) (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (fieldType : TypeRef) (item : ExpectedQueueItem ObjectRef)
    : expectedQueueItemFuelsAligned item
      -> (∀ segment,
            segment ∈ item.segments
            -> ∀ fuel,
                fuel ∈ segment.specFuels
                -> typeRefCompleteValueFuelBound fieldType < fuel)
      -> expectedPendingChildWorkToPending
            (expectedPendingChildWorkForItem schema resolvers fieldType item)
          = (buildFieldSlots schema fieldType item.toScheduleItem.segments
              (item.toScheduleItem.sources.map
                (fun source =>
                  resolvers.resolve item.key.parentType item.key.fieldName
                    item.key.arguments source))).fst := by
  intro haligned hready
  have hsegments :=
    slots_expectedPendingChildWorkForSegments_toPending_eq_buildFieldSlotsForResolvedSegments
      (ObjectRef := ObjectRef) schema resolvers item.key fieldType
      item.segments [] haligned hready
  have hsplit :
      splitResolvedBySegments item.toScheduleItem.segments
          (item.toScheduleItem.sources.map (fun source =>
            resolvers.resolve item.key.parentType item.key.fieldName
              item.key.arguments source)) =
        item.segments.map (fun segment =>
          ( segment.segment
          , segment.segment.sources.map (fun source =>
              resolvers.resolve item.key.parentType item.key.fieldName
                item.key.arguments source) )) := by
    unfold ExpectedQueueItem.toScheduleItem ScheduleItem.sources
    rw [List.map_flatten]
    simpa [Function.comp_def] using
      slots_splitResolvedBySegments_map_sources
        (ObjectRef := ObjectRef) item.segments
        (fun source =>
          resolvers.resolve item.key.parentType item.key.fieldName
            item.key.arguments source)
  rw [show buildFieldSlots schema fieldType item.toScheduleItem.segments
        (item.toScheduleItem.sources.map (fun source =>
          resolvers.resolve item.key.parentType item.key.fieldName
            item.key.arguments source)) =
      buildFieldSlotsForResolvedSegments schema fieldType
        (splitResolvedBySegments item.toScheduleItem.segments
          (item.toScheduleItem.sources.map (fun source =>
            resolvers.resolve item.key.parentType item.key.fieldName
              item.key.arguments source)))
        [] by
      simp [buildFieldSlots, buildFieldSlotsLoop]]
  rw [hsplit]
  simpa [expectedPendingChildWorkForItem, ExpectedQueueItem.toScheduleItem,
    expectedPendingChildWorkToPending] using hsegments

end ExecutionBreadth

end Algorithms

end GraphQL
