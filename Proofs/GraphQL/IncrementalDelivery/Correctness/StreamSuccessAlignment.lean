import Proofs.GraphQL.IncrementalDelivery.Correctness.ValueFailureCoverage
import Proofs.GraphQL.IncrementalDelivery.Correctness.EntryCoverageRetention

/-! Nonbubbling ordinary list execution keeps every actual mixed stream item available. -/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution
open Semantics

attribute [local simp] id_pure_eq id_bind_eq id_map_eq run_bind run_map

-----------------------------------------------------------------------------------------
-- Actual threaded item completion aligns with ordinary reference values
-----------------------------------------------------------------------------------------

/-- Ordinary successful list execution prevents mixed stream short-circuiting.
Witness: input-list descent and forward bubbling preservation at each actual threaded
state. Every reference item has the corresponding actual retained completion at its
absolute response index, with its child work unchanged. Data and error counts may differ;
successful partial items can retain failed deferred children.
-/
theorem completeStreamItems_aligns_ordinarySuccess (schema : Schema)
    (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
    (itemType : TypeRef) (selected : List FieldDetails)
    (values : List (ResolverValue ObjectRef))
    (valid : ∀ field ∈ selected, ArgumentValidity.FieldArgumentsValid variables field)
    (path : ResponsePath) (index state : Nat) (reference : List ResponseValue)
    (errors : Nat)
    (success
      : GraphQL.Execution.completeValueList schema resolvers variables fuel itemType
          (selected.map eraseField) values
        = .ok (reference, errors))
    : let items :=
        ((completeStreamItems schema resolvers variables fuel itemType selected
            values path index).run
          state).1
      items.length = values.length
      ∧ ∀ offset data,
          reference[offset]? = some data
          → ∃ resolved ordinaryErrors itemState,
              values[offset]? = some resolved
              ∧ GraphQL.Execution.completeValue schema resolvers variables fuel itemType
                  (selected.map eraseField) resolved
                = .ok (data, ordinaryErrors)
              ∧ let completed :=
                  ((completeValue schema resolvers variables fuel itemType selected
                      resolved (path ++ [.index (index + offset)]) [] [] false).run
                    itemState).1
                items[offset]? = some (completed.result, completed.work)
                ∧ ∃ initial count, completed.result = .ok (initial, count) := by
  induction values generalizing index state reference errors with
  | nil =>
      have empty : reference = [] := by
        have equation := success
        simp only [GraphQL.Execution.completeValueList, Except.ok.injEq, Prod.mk.injEq]
          at equation
        exact equation.1.symm
      subst reference
      exact ⟨by simp [completeStreamItems], by intro offset data member; simp at member⟩
  | cons value rest ih =>
      cases ordinaryHead
            : GraphQL.Execution.completeValue schema resolvers variables fuel
                itemType (selected.map eraseField) value with
      | error count =>
          cases ordinaryTail : GraphQL.Execution.completeValueList schema resolvers variables
              fuel itemType (selected.map eraseField) rest <;>
            simp [GraphQL.Execution.completeValueList, ordinaryHead, ordinaryTail,
              Result.combine] at success
      | ok pair =>
          obtain ⟨headData, headErrors⟩ := pair
          cases ordinaryTail
                : GraphQL.Execution.completeValueList schema resolvers variables
                    fuel itemType (selected.map eraseField) rest with
          | error count =>
              simp [GraphQL.Execution.completeValueList, ordinaryHead, ordinaryTail,
                Result.combine] at success
          | ok pair =>
              obtain ⟨tailData, tailErrors⟩ := pair
              have referenceEq : reference = headData :: tailData := by
                have equation := success
                simp only [GraphQL.Execution.completeValueList, ordinaryHead, ordinaryTail,
                  Result.combine, Except.ok.injEq, Prod.mk.injEq] at equation
                exact equation.1.symm
              subst reference
              let action := completeValue schema resolvers variables fuel itemType selected
                value (path ++ [.index index]) [] [] false
              let completed := (action.run state).1
              let next := (action.run state).2
              obtain ⟨initial, count, initialSuccess⟩ :=
                completeValue_initialSuccess_of_ordinarySuccess schema resolvers variables
                  fuel itemType selected value valid (path ++ [.index index]) [] [] false
                  state headData headErrors ordinaryHead
              change completed.result = .ok (initial, count) at initialSuccess
              have retained : ((completeStreamItems schema resolvers variables fuel itemType
                  selected (value :: rest) path index).run state).1
                  = (completed.result, completed.work) ::
                    ((completeStreamItems schema resolvers variables fuel itemType selected
                      rest path (index + 1)).run next).1 := by
                simp [completeStreamItems, action, next, completed, initialSuccess]
              obtain ⟨tailLength, tailAligned⟩ := ih (index + 1) next tailData tailErrors
                ordinaryTail
              dsimp only
              rw [retained]
              refine ⟨by simp only [List.length_cons, tailLength], ?_⟩
              intro offset data member
              cases offset with
              | zero =>
                  simp only [List.getElem?_cons_zero, Option.some.injEq] at member
                  subst data
                  refine ⟨value, headErrors, state, rfl, ordinaryHead, ?_⟩
                  simp only [Nat.add_zero, List.getElem?_cons_zero]
                  change some (completed.result, completed.work)
                    = some (completed.result, completed.work)
                    ∧ ∃ initial count, completed.result = .ok (initial, count)
                  exact ⟨rfl, initial, count, initialSuccess⟩
              | succ offset =>
                  simp only [List.getElem?_cons_succ] at member
                  obtain ⟨resolved, ordinaryErrors, itemState, found, ordinary, retained,
                    successful⟩ := tailAligned offset data member
                  refine ⟨resolved, ordinaryErrors, itemState, ?_, ordinary, ?_⟩
                  · simpa only [List.getElem?_cons_succ] using found
                  · have indices : index + 1 + offset = index + offset.succ := by omega
                    rw [indices] at retained successful
                    exact ⟨retained, successful⟩

-----------------------------------------------------------------------------------------
-- The full streamed-tail comparison reduces to the ordinary-success value witnesses
-----------------------------------------------------------------------------------------

/-- Per-value mixed coverage suffices for every entry of an actual nonbubbling stream tail.
Witness: reference item membership, actual threaded alignment, and retention at that
same ordinal. `coverage` is the recursive pure-value proof obligation, not an additional
queue contract or public correctness premise; `RecursiveValueCoverage` discharges it.
-/
theorem completeStreamItems_entriesCovered_of_values (schema : Schema)
    (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
    (itemType : TypeRef) (selected : List FieldDetails)
    (values : List (ResolverValue ObjectRef))
    (valid : ∀ field ∈ selected, ArgumentValidity.FieldArgumentsValid variables field)
    (path : ResponsePath) (index state : Nat) (reference : List ResponseValue)
    (errors : Nat)
    (success
      : GraphQL.Execution.completeValueList schema resolvers variables fuel itemType
          (selected.map eraseField) values
        = .ok (reference, errors))
    (node : DeliveryNode) (atPath : node.path = path)
    (cursors : ResponsePositions.Cursors)
    (cursor : ResponsePositions.cursorAt cursors node.path = some index)
    (containers : Bool)
    (coverage
      : ∀ resolved ∈ values,
          ∀ offset itemState data ordinaryErrors,
            GraphQL.Execution.completeValue schema resolvers variables fuel itemType
                (selected.map eraseField) resolved
              = .ok (data, ordinaryErrors)
            → let completed :=
                ((completeValue schema resolvers variables fuel itemType selected
                    resolved (path ++ [.index (index + offset)]) [] [] false).run
                  itemState).1
              EntriesCovered containers
                (TypedResponse.value (path ++ [.index (index + offset)]) data)
                (DeliveryPaths.result
                    (ResponsePositions.value containers
                      (path ++ [.index (index + offset)]))
                    completed.result
                  ++ (sourceTasks [] none
                        (Semantics.MixedPaths.resultCursors
                          (ResponsePositions.listCursors
                            (path ++ [.index (index + offset)]))
                          completed.result) completed.work).flatMap
                      (SourceTask.positions containers))
                completed.work)
    : let items :=
        ((completeStreamItems schema resolvers variables fuel itemType selected
            values path index).run
          state).1
      EntriesCovered containers (TypedResponse.items path index reference)
        ((sourceTasks [] none cursors (.stream node items)).flatMap
          (SourceTask.positions containers)) (.stream node items) := by
  subst path
  obtain ⟨_, aligned⟩ := completeStreamItems_aligns_ordinarySuccess schema resolvers variables
    fuel itemType selected values valid node.path index state reference errors success
  dsimp only
  intro entry member visible
  obtain ⟨offset, data, foundReference, inValue⟩ :=
    TypedResponse.items_entry_member node.path index reference entry member
  obtain ⟨resolved, ordinaryErrors, itemState, foundInput, ordinary, retained,
    initial, count, initialSuccess⟩ := aligned offset data foundReference
  have covered := coverage resolved (List.mem_iff_getElem?.mpr ⟨offset, foundInput⟩)
    offset itemState data ordinaryErrors ordinary
  dsimp only at covered initialSuccess retained
  rw [initialSuccess, DeliveryPaths.result, Semantics.MixedPaths.resultCursors] at covered
  have retainedSuccess := retained
  rw [initialSuccess] at retainedSuccess
  exact (EntriesCovered.streamItem covered cursor retainedSuccess) entry inValue visible

-----------------------------------------------------------------------------------------
-- Ordinary null items have actual stream-data or retained-child-failure explanations
-----------------------------------------------------------------------------------------

/-- Every ordinary null item is covered in the actual mixed stream's source or failures.
Witness: ordinary-success alignment identifies its actual completion; local mixed null
reflection and stream retention preserve its explanation. Nullable errors and failed
deferred descendants need no equality of initial and ordinary values or error counts.
-/
theorem completeStreamItems_nullEntry_covered (schema : Schema)
    (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
    (itemType : TypeRef) (selected : List FieldDetails)
    (values : List (ResolverValue ObjectRef))
    (valid : ∀ field ∈ selected, ArgumentValidity.FieldArgumentsValid variables field)
    (path : ResponsePath) (index state : Nat) (reference : List ResponseValue)
    (errors : Nat)
    (success
      : GraphQL.Execution.completeValueList schema resolvers variables fuel itemType
          (selected.map eraseField) values
        = .ok (reference, errors))
    (node : DeliveryNode) (atPath : node.path = path)
    (cursors : ResponsePositions.Cursors)
    (cursor : ResponsePositions.cursorAt cursors node.path = some index) (offset : Nat)
    (isNull : reference[offset]? = some .null) (containers : Bool)
    : let items :=
        ((completeStreamItems schema resolvers variables fuel itemType selected
            values path index).run
          state).1
      EntryExplained
        ((sourceTasks [] none cursors (.stream node items)).flatMap
          (SourceTask.positions containers)) (.stream node items)
        (path ++ [.index (index + offset)], .null) := by
  subst path
  obtain ⟨_, aligned⟩ := completeStreamItems_aligns_ordinarySuccess schema resolvers variables
    fuel itemType selected values valid node.path index state reference errors success
  obtain ⟨resolved, ordinaryErrors, itemState, _, ordinaryNull, retained,
    initial, count, initialSuccess⟩ := aligned offset .null isNull
  let completed := ((completeValue schema resolvers variables fuel itemType selected
    resolved (node.path ++ [.index (index + offset)]) [] [] false).run itemState).1
  change completed.result = .ok (initial, count) at initialSuccess
  have localCovered := completeValue_nullEntry_covered schema resolvers variables fuel
    itemType selected resolved valid (node.path ++ [.index (index + offset)]) [] [] false
    itemState ordinaryErrors ordinaryNull containers
    ((sourceTasks [] none (ResponsePositions.listCursors
      (node.path ++ [.index (index + offset)]) initial) completed.work).flatMap
        (SourceTask.positions containers))
  change EntryExplained
    (DeliveryPaths.result (ResponsePositions.value containers
      (node.path ++ [.index (index + offset)])) completed.result
      ++ (sourceTasks [] none (ResponsePositions.listCursors
        (node.path ++ [.index (index + offset)]) initial) completed.work).flatMap
          (SourceTask.positions containers)) completed.work
    (node.path ++ [.index (index + offset)], .null) at localCovered
  rw [initialSuccess, DeliveryPaths.result] at localCovered
  have retainedSuccess := retained
  change _ = some (completed.result, completed.work) at retainedSuccess
  rw [initialSuccess] at retainedSuccess
  exact (localCovered.streamItem_child node _ offset completed.result retained).available_mono
    (preparedValuePositions_in_stream cursor retainedSuccess)

end GraphQL.IncrementalDelivery.Correctness
