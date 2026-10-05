import Proofs.GraphQL.IncrementalDelivery.Correctness.ListExecutionCoverage
import Proofs.GraphQL.IncrementalDelivery.Correctness.StreamSuccessAlignment

/-! The initial list prefix and actual streamed tail cover the ordinary reference list. -/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution
open Semantics
open Semantics.MixedPaths

attribute [local simp] id_pure_eq id_bind_eq id_map_eq run_bind run_map

-----------------------------------------------------------------------------------------
-- Prefix/tail assembly retains real source coordinates and actual failure evidence
-----------------------------------------------------------------------------------------

/-- A covered initial prefix and actual streamed tail cover the full reference list.
Witness: enclosing-list cursor extension preserves prefix sources, while combined source
inventories preserve the tail. Reference and actual prefix lengths share the tail offset.
-/
theorem EntriesCovered.streamPrefix {containers path initialWork slices streamWork}
    (referencePrefix referenceTail initial : List ResponseValue)
    (prefixCovered
      : EntriesCovered containers (TypedResponse.items path 0 referencePrefix)
          (preparedItemPositions containers path 0 initial initialWork) initialWork)
    (prefixSeed
      : WorkCursorSeed (ResponsePositions.itemCursors path 0 initial) initialWork slices)
    (sameLength : referencePrefix.length = initial.length)
    (tailCovered
      : EntriesCovered containers
          (TypedResponse.items path initial.length referenceTail)
          ((sourceTasks [] none (ResponsePositions.listCursors path (.list initial))
              streamWork).flatMap
            (SourceTask.positions containers)) streamWork)
    : EntriesCovered containers
        (TypedResponse.value path (.list (referencePrefix ++ referenceTail)))
        (preparedValuePositions containers path (.list initial)
          (.combine initialWork streamWork)) (.combine initialWork streamWork) := by
  have prefixList := prefixCovered.list referencePrefix initial prefixSeed
  have prefix' := (prefixList.combine_left streamWork).available_mono
    (show (preparedValuePositions containers path (.list initial) initialWork).Subset
        (preparedValuePositions containers path (.list initial)
          (.combine initialWork streamWork)) from by
      unfold preparedValuePositions
      rw [sourcePositions_combine]
      intro position member
      simp only [List.mem_append] at member ⊢
      exact member.elim Or.inl (fun future => Or.inr (Or.inl future)))
  have tail' := (tailCovered.combine_right initialWork).available_mono
    (show ((sourceTasks [] none (ResponsePositions.listCursors path (.list initial))
        streamWork).flatMap (SourceTask.positions containers)).Subset
        (preparedValuePositions containers path (.list initial)
          (.combine initialWork streamWork)) from by
      unfold preparedValuePositions
      rw [sourcePositions_combine]
      exact fun _ member => List.mem_append_right _ (List.mem_append_right _ member))
  rw [TypedResponse.value, TypedResponse.items_append, Nat.zero_add, sameLength,
    ← List.cons_append]
  exact EntriesCovered.append_iff.mpr ⟨prefix', tail'⟩

-----------------------------------------------------------------------------------------
-- Actual stream hook: full ordinary list success keeps both finite partitions available
-----------------------------------------------------------------------------------------

/-- An ordinary successful list is covered by the actual initial prefix and streamed tail.
Witness: ordinary take/drop result composition, actual prefix success and length, and
actual streamed-item alignment. The retained boundary may have an empty tail; initial and
reference data/error counts are not equated.
-/
theorem completeListValueWithStream_listEntriesCovered_of_values (containers : Bool)
    (schema : Schema) (resolvers : Resolvers ObjectRef) (variables : VariableValues)
    (fuel : Nat)
    (valuesCovered : ValueCompletionCoverage containers schema resolvers variables fuel)
    (itemType : TypeRef) (selected : List FieldDetails)
    (values : List (ResolverValue ObjectRef))
    (valid : ∀ field ∈ selected, ArgumentValidity.FieldArgumentsValid variables field)
    (path : ResponsePath) (usages : WorkQueueSemantics.NodeRefs) (deferMap : DeferMap)
    (allowStream : Bool) (reference : List ResponseValue) (errors : Nat)
    (success
      : GraphQL.Execution.completeValueList schema resolvers variables fuel itemType
          (selected.map eraseField) values
        = .ok (reference, errors))
    : RunEnsures
        (fun completed =>
          ∃ initial count,
            completed.result = .ok (.list initial, count)
            ∧ EntriesCovered containers (TypedResponse.value path (.list reference))
                (preparedValuePositions containers path (.list initial) completed.work)
                completed.work)
        (completeListValueWithStream schema resolvers variables fuel itemType selected
          values path usages deferMap allowStream) := by
  obtain ⟨usage, usageEq⟩ := ArgumentValidity.fields_getStreamUsage_ok variables selected valid
  have hook : (if allowStream then getStreamUsage variables
      (selected.head?.map FieldDetails.directives |>.getD []) else .ok none)
      = .ok (if allowStream then usage else none) := by cases allowStream <;> simp [usageEq]
  cases active : (if allowStream then usage else none) with
  | none =>
      intro state
      have compared := completeListValue_entriesCovered_of_values containers schema resolvers
        variables fuel valuesCovered itemType selected values valid path 0 usages deferMap state
      obtain ⟨initial, count, actualSuccess, covered⟩ := compared reference errors success
      obtain ⟨slices, seeded, _⟩ := completeListValue_seeded schema resolvers variables fuel
        itemType selected values path 0 usages deferMap state
      simp only [actualSuccess, resultCursors] at seeded
      refine ⟨initial, count, ?_, ?_⟩
      · simp only [completeListValueWithStream, hook, active, run_bind, StateT.run_pure,
          id_pure_eq, Completion.catchNull, actualSuccess]
      · simpa only [completeListValueWithStream, hook, active, run_bind, StateT.run_pure,
          id_pure_eq, Completion.catchNull, actualSuccess]
          using covered.list reference initial seeded
  | some usage =>
      have split := SourceReconstruction.basicList_split_result schema resolvers variables
        fuel itemType (selected.map eraseField) values usage.initialCount
      rw [success] at split
      cases first : GraphQL.Execution.completeValueList schema resolvers variables fuel
          itemType (selected.map eraseField) (values.take usage.initialCount) <;>
        cases last : GraphQL.Execution.completeValueList schema resolvers variables fuel
          itemType (selected.map eraseField) (values.drop usage.initialCount) <;>
        simp only [first, last, Result.combine, Except.ok.injEq, Prod.mk.injEq, reduceCtorEq,
          List.append_eq] at split
      rename_i head tail
      have refEq := split.1
      subst reference
      simp only [completeListValueWithStream, hook, active]
      refine runEnsures_bind (fun initial =>
        ItemsCompletionCovered containers path 0
          (GraphQL.Execution.completeValueList schema resolvers variables fuel itemType
            (selected.map eraseField) (values.take usage.initialCount)) initial
        ∧ SeedOwnsCompletion (DeliveryPaths.items true path 0)
          (ResponsePositions.itemCursors path 0)
          (UnderItemRange path 0 (values.take usage.initialCount).length) initial
        ∧ ∀ data errors, initial.result = .ok (data, errors)
          → data.length = (values.take usage.initialCount).length) _ _ _ ?_ ?_
      · intro state
        refine ⟨completeListValue_entriesCovered_of_values containers schema resolvers variables
            fuel valuesCovered itemType selected (values.take usage.initialCount) valid path 0
            usages deferMap state,
          ?_,
          completeListValue_result_length schema resolvers variables fuel itemType
            selected (values.take usage.initialCount) path 0 usages deferMap state⟩
        simpa only [Nat.zero_add] using completeListValue_seeded schema resolvers variables
          fuel itemType selected (values.take usage.initialCount) path 0 usages deferMap state
      · intro initial compared
        obtain ⟨data, count, actualSuccess, prefixCovered⟩ := compared.1 head.1 head.2 first
        obtain ⟨slices, prefixSeed, _⟩ := compared.2.1
        simp only [actualSuccess, resultCursors] at prefixSeed
        have length := compared.2.2 data count actualSuccess
        have referenceLength := SourceReconstruction.basicList_length schema resolvers variables
          fuel itemType (selected.map eraseField) (values.take usage.initialCount) head.1
          head.2 first
        simp only [actualSuccess]
        split
        · rename_i exhausted
          have tailEmpty : tail.1 = [] := by
            have empty : values.drop usage.initialCount = [] :=
              List.drop_eq_nil_iff.mpr (by omega)
            simp only [empty, GraphQL.Execution.completeValueList, Except.ok.injEq] at last
            exact (congrArg Prod.fst last).symm
          apply runEnsures_pure
          refine ⟨data, count, ?_, ?_⟩
          · simp [Completion.catchNull, actualSuccess]
          · simpa only [tailEmpty, List.append_nil, Completion.catchNull, actualSuccess]
              using prefixCovered.list head.1 data prefixSeed
        · rename_i retained
          have countBound : usage.initialCount ≤ values.length := by omega
          have prefixLength : data.length = usage.initialCount := by
            simpa only [List.length_take, Nat.min_eq_left countBound] using length
          have sameLength : head.1.length = data.length := referenceLength.trans length.symm
          refine runEnsures_bind (fun _ : NodeRef => True) _ _ _ (fun _ => trivial) ?_
          intro ref _
          let streamFields := selected.map (fun field => { field with deferUsage := none })
          have streamValid : ∀ field ∈ streamFields,
              ArgumentValidity.FieldArgumentsValid variables field := by
            intro field member
            obtain ⟨original, originalMember, same⟩ := List.mem_map.mp member
            rw [← same]
            exact valid original originalMember
          have erasure : streamFields.map eraseField = selected.map eraseField := by
            simp [streamFields, List.map_map, eraseField]
          let node : DeliveryNode := { ref := ref, path := path, label := usage.label }
          let cursors := ResponsePositions.listCursors path (.list data)
          have cursor
              : ResponsePositions.cursorAt cursors node.path
                = some usage.initialCount := by
            simp [cursors, node, ResponsePositions.listCursors, ResponsePositions.cursorAt,
              prefixLength]
          refine runEnsures_bind (fun items => EntriesCovered containers
            (TypedResponse.items path usage.initialCount tail.1)
            ((sourceTasks [] none cursors (.stream node items)).flatMap
              (SourceTask.positions containers)) (.stream node items)) _ _ _ ?_ ?_
          · intro state
            apply completeStreamItems_entriesCovered_of_values schema resolvers variables fuel
              itemType streamFields (values.drop usage.initialCount) streamValid path
              usage.initialCount state tail.1 tail.2 (by simpa only [erasure] using last)
              node rfl cursors cursor containers
            intro resolved _ offset itemState value ordinaryErrors ordinarySuccess
            obtain ⟨initialValue, initialCount, valueSuccess, covered⟩ :=
              valuesCovered itemType streamFields resolved streamValid
                (path ++ [.index (usage.initialCount + offset)]) [] [] false itemState
                value ordinaryErrors ordinarySuccess
            dsimp only
            rw [valueSuccess, DeliveryPaths.result, resultCursors]
            exact covered
          · intro items tailCovered
            apply runEnsures_pure
            refine ⟨data, count, ?_, ?_⟩
            · simp [Completion.catchNull, actualSuccess]
            · simp only [Completion.catchNull, actualSuccess]
              apply EntriesCovered.streamPrefix head.1 tail.1 data prefixCovered prefixSeed
                sameLength
              simpa only [prefixLength] using tailCovered

/-- Actual stream-hook completion is covered from recursive value coverage.
Witness: successful ordinary lists use actual prefix/tail assembly; ordinary nullable
list bubbles use forward initial-success preservation and actual failed-task reflection.
Neither branch assumes zero errors or agreement of counted errors.
-/
theorem completeListValueWithStream_entriesCovered_of_values (containers : Bool)
    (schema : Schema) (resolvers : Resolvers ObjectRef) (variables : VariableValues)
    (fuel : Nat)
    (valuesCovered : ValueCompletionCoverage containers schema resolvers variables fuel)
    (itemType : TypeRef) (selected : List FieldDetails)
    (values : List (ResolverValue ObjectRef))
    (valid : ∀ field ∈ selected, ArgumentValidity.FieldArgumentsValid variables field)
    (path : ResponsePath) (usages : WorkQueueSemantics.NodeRefs) (deferMap : DeferMap)
    (allowStream : Bool)
    : RunEnsures
        (ValueCompletionCovered containers path
          (GraphQL.Execution.catchBubbleAsNull ResponseValue.list
            (GraphQL.Execution.completeValueList schema resolvers variables fuel itemType
              (selected.map eraseField) values)))
        (completeListValueWithStream schema resolvers variables fuel itemType selected
          values path usages deferMap allowStream) := by
  intro state reference errors success
  cases ordinary
        : GraphQL.Execution.completeValueList schema resolvers variables fuel itemType
            (selected.map eraseField) values with
  | ok pair =>
      have same : reference = .list pair.1 := by
        simp only [ordinary, GraphQL.Execution.catchBubbleAsNull, Except.ok.injEq,
          Prod.mk.injEq] at success
        exact success.1.symm
      subst reference
      obtain ⟨initial, count, actual, covered⟩ :=
        completeListValueWithStream_listEntriesCovered_of_values containers schema resolvers
          variables fuel valuesCovered itemType selected values valid path usages deferMap
          allowStream pair.1 pair.2 ordinary state
      exact ⟨.list initial, count, actual, covered⟩
  | error count =>
      have same : reference = .null := by
        simp only [ordinary, GraphQL.Execution.catchBubbleAsNull, Except.ok.injEq,
          Prod.mk.injEq] at success
        exact success.1.symm
      subst reference
      have preserved := InitialFailures.completeListValueWithStream_preserves_failures schema
        resolvers variables fuel itemType selected values valid path usages deferMap allowStream
        state
      have reflected := OrdinaryFailures.completeListValueWithStream_explains_failures schema
        resolvers variables fuel itemType selected values valid path usages deferMap allowStream
        state
      obtain ⟨initial, initialCount, initialSuccess⟩ := preserved.1.initial_success .null errors
        success
      refine ⟨initial, initialCount, initialSuccess, ?_⟩
      have covered := nullEntry_explained preserved.1 reflected errors success containers
        ((sourceTasks [] none (resultCursors (ResponsePositions.listCursors path)
          ((completeListValueWithStream schema resolvers variables fuel itemType selected values
            path usages deferMap allowStream).run state).1.result)
          ((completeListValueWithStream schema resolvers variables fuel itemType selected values
            path usages deferMap allowStream).run state).1.work).flatMap
            (SourceTask.positions containers))
      rw [initialSuccess, DeliveryPaths.result, resultCursors] at covered
      intro entry member _
      obtain rfl := List.mem_singleton.mp member
      exact covered

end GraphQL.IncrementalDelivery.Correctness
