import Proofs.GraphQL.IncrementalDelivery.Correctness.ValueWrapperCoverage

/-! Actual list completion preserves failure-aware item coverage at absolute offsets. -/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution
open Semantics
open Semantics.MixedPaths

attribute [local simp] id_pure_eq id_bind_eq id_map_eq run_bind run_map

-----------------------------------------------------------------------------------------
-- Proof-only list comparison and actual head/tail composition
-----------------------------------------------------------------------------------------

/-- Every ordinary successful item list has a successful covered initial item list.
The absolute offset is shared; actual data and counted errors need not match the reference.
-/
def ItemsCompletionCovered (containers : Bool) (path : ResponsePath) (index : Nat)
    (ordinary : Result (List ResponseValue)) (completed : Completion (List ResponseValue))
    : Prop :=
  ∀ reference errors,
    ordinary = .ok (reference, errors)
    → ∃ initial count,
        completed.result = .ok (initial, count)
        ∧ EntriesCovered containers (TypedResponse.items path index reference)
            (preparedItemPositions containers path index initial completed.work)
            completed.work

/-- Equal item results are covered by their actual initial positions at any offset.
Witness: successful-result identification and the typed/visible item-path equation.
-/
theorem ItemsCompletionCovered.of_result_eq {containers path index ordinary completed}
    (same : completed.result = ordinary)
    : ItemsCompletionCovered containers path index ordinary completed := by
  intro reference errors success
  refine ⟨reference, errors, same.trans success, ?_⟩
  apply EntriesCovered.of_visiblePaths_subset
  rw [visibleEntryPaths_items]
  exact fun _ member => List.mem_append_left _ member

/-- Covered head and tail completions compose at consecutive absolute item offsets.
Witness: actual successful parts, seeded child inventories, and unique assembled initial
positions. Every retained failed-task explanation survives work combination.
-/
theorem ItemsCompletionCovered.cons
    {containers path index ordinaryHead ordinaryTail head tail headSlices tailSlices}
    (headCovered
      : ValueCompletionCovered containers (path ++ [.index index]) ordinaryHead head)
    (tailCovered : ItemsCompletionCovered containers path (index + 1) ordinaryTail tail)
    (headSeed
      : WorkCursorSeed
          (resultCursors (ResponsePositions.listCursors (path ++ [.index index]))
            head.result)
          head.work headSlices)
    (tailSeed
      : WorkCursorSeed
          (resultCursors (ResponsePositions.itemCursors path (index + 1)) tail.result)
          tail.work tailSlices)
    (unique
      : ∀ initial count,
          (Completion.combine List.cons head tail).result = .ok (initial, count)
          → (ResponsePositions.items true path index initial).Nodup)
    : ItemsCompletionCovered containers path index
        (Result.combine List.cons ordinaryHead ordinaryTail)
        (Completion.combine List.cons head tail) := by
  intro reference errors success
  cases first : ordinaryHead <;> cases last : ordinaryTail <;>
    simp only [first, last, Result.combine, Except.ok.injEq, Prod.mk.injEq, reduceCtorEq]
      at success
  rename_i value rest
  obtain ⟨rfl, _⟩ := success
  obtain ⟨initialHead, headErrors, headSuccess, coversHead⟩ := headCovered _ _ first
  obtain ⟨initialTail, tailErrors, tailSuccess, coversTail⟩ := tailCovered _ _ last
  have combined : (Completion.combine List.cons head tail).result
      = .ok (initialHead :: initialTail, headErrors + tailErrors) := by
    simp [Completion.combine, headSuccess, tailSuccess, Result.combine]
  refine ⟨initialHead :: initialTail, headErrors + tailErrors, combined, ?_⟩
  simp only [Completion.combine, headSuccess, tailSuccess, Result.combine]
  have headSeed' : WorkCursorSeed (ResponsePositions.itemCursors path index [initialHead])
      head.work headSlices := by
    simpa only [headSuccess, resultCursors, ResponsePositions.itemCursors,
      List.append_nil]
      using headSeed
  have tailSeed' : WorkCursorSeed (ResponsePositions.itemCursors path (index + 1) initialTail)
      tail.work tailSlices := by
    simpa only [tailSuccess, resultCursors] using tailSeed
  have covered := EntriesCovered.append_items [initialHead] initialTail
    (leftReference := TypedResponse.value (path ++ [.index index]) value.1)
    (rightReference := TypedResponse.items path (index + 1) rest.1)
    (by simpa only [preparedItemPositions_singleton] using coversHead)
    (by simpa only [List.length_singleton] using coversTail)
    headSeed' (by simpa only [List.length_singleton] using tailSeed')
    (by simpa only [List.singleton_append] using unique _ _ combined)
  simpa only [TypedResponse.items, List.singleton_append] using covered

-----------------------------------------------------------------------------------------
-- Actual list traversal uses the recursive value comparison at its threaded states
-----------------------------------------------------------------------------------------

/-- Actual finite list completion is covered from the recursive value-completion witness.
Witness: input-list induction at the actual threaded state and absolute item index.
Generated cursor/ownership certificates supply assembly uniqueness, with errors allowed.
-/
theorem completeListValue_entriesCovered_of_items (containers : Bool) (schema : Schema)
    (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
    (itemType : TypeRef) (selected : List FieldDetails)
    (values : List (ResolverValue ObjectRef))
    (path : ResponsePath) (index : Nat) (usages : WorkQueueSemantics.NodeRefs)
    (deferMap : DeferMap)
    (itemsCovered
      : ∀ resolved itemPath,
          RunEnsures
            (ValueCompletionCovered containers itemPath
              (GraphQL.Execution.completeValue schema resolvers variables fuel itemType
                (selected.map eraseField) resolved))
            (completeValue schema resolvers variables fuel itemType selected resolved
              itemPath usages deferMap false))
    : RunEnsures
        (ItemsCompletionCovered containers path index
          (GraphQL.Execution.completeValueList schema resolvers variables fuel itemType
            (selected.map eraseField) values))
        (completeListValue schema resolvers variables fuel itemType selected values path
          index usages deferMap) := by
  induction values generalizing index with
  | nil =>
      intro state
      apply ItemsCompletionCovered.of_result_eq
      simp [completeListValue, GraphQL.Execution.completeValueList, Completion.pure]
  | cons resolved rest ih =>
      intro state
      let headAction := completeValue schema resolvers variables fuel itemType selected
        resolved (path ++ [.index index]) usages deferMap false
      let head := (headAction.run state).1
      let next := (headAction.run state).2
      let tail := ((completeListValue schema resolvers variables fuel itemType selected rest
        path (index + 1) usages deferMap).run next).1
      have coversHead := itemsCovered resolved (path ++ [.index index]) state
      have coversTail := ih (index + 1) next
      obtain ⟨headSlices, headSeed, _⟩ := completeValue_seeded schema resolvers variables fuel
        itemType selected resolved (path ++ [.index index]) usages deferMap false state
      obtain ⟨tailSlices, tailSeed, _⟩ := completeListValue_seeded schema resolvers variables
        fuel itemType selected rest path (index + 1) usages deferMap next
      have assembled := completeListValue_seeded schema resolvers variables fuel itemType
        selected (resolved :: rest) path index usages deferMap state
      simp only [completeListValue, run_bind, StateT.run_pure, id_pure_eq] at assembled ⊢
      change SeedOwnsCompletion _ _ _ (Completion.combine List.cons head tail) at assembled
      simp only [GraphQL.Execution.completeValueList]
      apply ItemsCompletionCovered.cons coversHead coversTail headSeed tailSeed
      intro initial count success
      change (Completion.combine List.cons head tail).result = .ok (initial, count) at success
      obtain ⟨_, _, owned⟩ := assembled
      have unique := (List.nodup_append.mp owned.1).1
      change (DeliveryPaths.result (DeliveryPaths.items true path index)
        (Completion.combine List.cons head tail).result).Nodup at unique
      simpa only [success, DeliveryPaths.result, source_items_eq_positions] using unique

/-- The general recursive value witness discharges the actual list-item dependency.
Witness: specializing value coverage to this list's item type, fields, and enclosing
context; the checked list traversal supplies offsets, seeding, and initial uniqueness.
-/
theorem completeListValue_entriesCovered_of_values (containers : Bool) (schema : Schema)
    (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
    (valuesCovered : ValueCompletionCoverage containers schema resolvers variables fuel)
    (itemType : TypeRef) (selected : List FieldDetails)
    (values : List (ResolverValue ObjectRef))
    (valid : ∀ field ∈ selected, ArgumentValidity.FieldArgumentsValid variables field)
    (path : ResponsePath) (index : Nat) (usages : WorkQueueSemantics.NodeRefs)
    (deferMap : DeferMap)
    : RunEnsures
        (ItemsCompletionCovered containers path index
          (GraphQL.Execution.completeValueList schema resolvers variables fuel itemType
            (selected.map eraseField) values))
        (completeListValue schema resolvers variables fuel itemType selected values path
          index usages deferMap) :=
  completeListValue_entriesCovered_of_items containers schema resolvers variables fuel
    itemType selected values path index usages deferMap
    (fun resolved itemPath =>
      valuesCovered itemType selected resolved valid itemPath usages deferMap false)

-----------------------------------------------------------------------------------------
-- Nullable list wrapping and the inactive-stream execution branch
-----------------------------------------------------------------------------------------

/-- Nullable list wrapping retains covered items and explains ordinary ancestor nulls.
Witness: seeded item work keeps its inventory under the enclosing list cursor. A bubble
is caught initially as null or explained by a real failed descendant of the partial list.
-/
theorem ItemsCompletionCovered.catchList {containers path ordinary completed slices}
    (covered : ItemsCompletionCovered containers path 0 ordinary completed)
    (seeded
      : WorkCursorSeed
          (resultCursors (ResponsePositions.itemCursors path 0) completed.result)
          completed.work slices)
    (reflected : OrdinaryFailures.BubblesExplained path ordinary completed)
    : ValueCompletionCovered containers path
        (GraphQL.Execution.catchBubbleAsNull ResponseValue.list ordinary)
        (completed.catchNull ResponseValue.list) := by
  intro reference errors success
  cases outcome : ordinary with
  | error count =>
      have referenceEq : reference = .null := by
        simp only [outcome, GraphQL.Execution.catchBubbleAsNull, Except.ok.injEq,
          Prod.mk.injEq] at success
        exact success.1.symm
      subst reference
      cases actual : completed.result with
      | error count =>
          refine ⟨.null, count, ?_, ?_⟩
          · simp [Completion.catchNull, actual]
          · simp only [Completion.catchNull, actual]
            apply EntriesCovered.of_visiblePaths_subset
            rw [visibleEntryPaths_value]
            exact fun _ member => List.mem_append_left _ member
      | ok pair =>
          obtain ⟨initial, count⟩ := pair
          refine ⟨.list initial, count, ?_, ?_⟩
          · simp [Completion.catchNull, actual]
          · rcases reflected _ outcome with initiallyFailed | retained
            · obtain ⟨count, failed⟩ := initiallyFailed
              simp [actual] at failed
            · obtain ⟨occurrence, owners, producer, payload, known, fails, below⟩ := retained
              intro entry member _
              obtain rfl := List.mem_singleton.mp member
              simp only [Completion.catchNull, actual]
              exact Or.inr ⟨occurrence, owners, producer, payload, known, fails,
                Or.inr ⟨rfl, below⟩⟩
  | ok pair =>
      have referenceEq : reference = .list pair.1 := by
        simp only [outcome, GraphQL.Execution.catchBubbleAsNull, Except.ok.injEq,
          Prod.mk.injEq] at success
        exact success.1.symm
      subst reference
      obtain ⟨initial, count, initialSuccess, covered⟩ := covered _ _ outcome
      have actualSeed : WorkCursorSeed (ResponsePositions.itemCursors path 0 initial)
          completed.work slices := by
        simpa only [initialSuccess, resultCursors] using seeded
      refine ⟨.list initial, count, ?_, ?_⟩
      · simp [Completion.catchNull, initialSuccess]
      · simpa only [Completion.catchNull, initialSuccess]
          using covered.list pair.1 initial actualSeed

/-- Actual nonstreaming list completion is covered from its recursive value witness.
Witness: actual finite item traversal, generated cursor seeds, and ordinary bubbling
reflection; nullable list catching retains exactly the resulting initial data and work.
-/
theorem completeListValueWithStream_entriesCovered_of_inactive (containers : Bool)
    (schema : Schema) (resolvers : Resolvers ObjectRef) (variables : VariableValues)
    (fuel : Nat)
    (valuesCovered : ValueCompletionCoverage containers schema resolvers variables fuel)
    (itemType : TypeRef) (selected : List FieldDetails)
    (values : List (ResolverValue ObjectRef))
    (valid : ∀ field ∈ selected, ArgumentValidity.FieldArgumentsValid variables field)
    (path : ResponsePath) (usages : WorkQueueSemantics.NodeRefs) (deferMap : DeferMap)
    (allowStream : Bool)
    (inactive
      : (if allowStream then
            getStreamUsage variables
              (selected.head?.map FieldDetails.directives |>.getD [])
          else
            .ok none)
        = .ok none)
    : RunEnsures
        (ValueCompletionCovered containers path
          (GraphQL.Execution.catchBubbleAsNull ResponseValue.list
            (GraphQL.Execution.completeValueList schema resolvers variables fuel itemType
              (selected.map eraseField) values)))
        (completeListValueWithStream schema resolvers variables fuel itemType selected
          values path usages deferMap allowStream) := by
  simp only [completeListValueWithStream, inactive]
  intro state
  have covered := completeListValue_entriesCovered_of_values containers schema resolvers
    variables fuel valuesCovered itemType selected values valid path 0 usages deferMap state
  obtain ⟨slices, seeded, _⟩ := completeListValue_seeded schema resolvers variables fuel itemType
    selected values path 0 usages deferMap state
  have reflected := OrdinaryFailures.completeListValue_explains_failures schema resolvers
    variables fuel itemType selected values valid path 0 usages deferMap state
  simpa only [run_bind, StateT.run_pure, id_pure_eq]
    using covered.catchList seeded reflected

end GraphQL.IncrementalDelivery.Correctness
