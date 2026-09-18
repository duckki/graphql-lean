import Proofs.GraphQL.IncrementalDelivery.Correctness.HistoryMerging
import Proofs.GraphQL.IncrementalDelivery.Correctness.WireAtomMerging
import Proofs.GraphQL.IncrementalDelivery.Correctness.SourceExecutionAttachments
import Proofs.GraphQL.IncrementalDelivery.Correctness.QueryCoverage
import Proofs.GraphQL.IncrementalDelivery.Correctness.QueryLifecycle
import Proofs.GraphQL.IncrementalDelivery.Correctness.TypedEquivalence

/-! Every successful complete query reconstructs its directive-erased ordinary response. -/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution
open WorkScheduler
open Semantics.MixedPaths
open SourceReconstruction SourceAttachments

/-- Complete zero-error work observations reconstruct their entire typed source
inventory. Witness: successful history merging, complete publication coverage, and
exact equivalence of the actual wire merger with absolute atom replay.
-/
theorem WorkObservation.merge_entries {paths bound response work result slices}
    (observed : WorkObservation response work true result)
    (coherent : Semantics.MixedOwnerPaths.WorkAt paths bound work)
    (positive : ExecutionErrors.WorkPositive work)
    (seeded : WorkCursorSeed (ResponsePositions.listCursors [] response.data) work slices)
    (unique : (ResponsePositions.value true [] response.data ++ slices.flatten).Nodup)
    (attached
      : WorkAttached (TypedResponse.value [] response.data) work
          (entryPaths
            ((sourceTasks [] none (ResponsePositions.listCursors [] response.data)
                work).map
              SourceTask.entries)))
    (zero : result.totalErrors = 0)
    : ∃ merged,
        mergeQueryResult result = some merged
        ∧ (TypedResponse.value [] merged.data).Perm
            (TypedResponse.value [] response.data
              ++ (sourceTasks [] none (ResponsePositions.listCursors [] response.data)
                    work).flatMap
                  SourceTask.entries) := by
  have safe := observed.idUsageValid
  have complete := observed.deliveryComplete
  have success := observed.workSuccess positive zero
  cases observed with
  | single empty =>
      have noTasks : sourceTasks [] none (ResponsePositions.listCursors [] response.data)
          work = [] := by
        apply List.eq_nil_iff_forall_not_mem.mpr
        intro task member
        obtain ⟨owners, known⟩ := sourceTasks_known .root _ member
        exact no_tasks_of_size_zero empty known
      exact ⟨response, rfl, by simp [noTasks]⟩
  | incremental groups streams batches nonempty batchNonempty admitted finished =>
      obtain ⟨events, matching, explained, _, batching, covered⟩ :=
        replayResponse_successful_history positive (finished rfl) zero
      have initialHistory : CursorHistory (ResponsePositions.listCursors [] response.data)
          (ResponsePositions.value true [] response.data) := by
        simpa only [source_value_eq_positions]
          using listCursors_positions [] response.data
      have sourceUnique : (ResponsePositions.value true [] response.data ++
          (sourceTasks [] none (ResponsePositions.listCursors [] response.data) work).flatMap
            (SourceTask.positions true)).Nodup := by
        simpa only [List.flatMap, sourceTasks_positions seeded] using unique
      obtain ⟨data, merged, entries, _⟩ := merge_history explained seeded success attached
        initialHistory (by simp only [TypedResponse.value_paths, source_value_eq_positions])
        sourceUnique events.length (Nat.le_refl _)
      have nodePaths : ∀ node ∈ (events ++ [WorkEvent.workQueueTermination]).flatMap
          eventNodes, paths node.key = node.path := by
        intro node member
        simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, eventNodes,
          List.append_nil] at member
        obtain ⟨kind, parents, birth, known⟩ := explained_nodes explained node member
        exact (workAt_node coherent known).2
      have atoms := workBatching_positionAtoms batching nodePaths
      have actual : applyAtoms (batches.flatten.flatten.flatMap eventPositionAtoms)
          response.data = some data := by
        rw [atoms]
        simpa [eventPositionAtoms] using merged
      have typedCoverage := (sourcePrefixTasks_perm
        (initial := ResponsePositions.listCursors [] response.data) explained
        (fun occurrence owners producer payload known =>
          (covered occurrence owners producer payload known).1)).flatMap_right SourceTask.entries
      refine ⟨{data, errors := 0}, ?_, entries.trans (typedCoverage.append_left _)⟩
      rw [replayResponse_merge_atoms coherent admitted safe complete, actual]
      simp only [Option.map_some, zero]

/-- Root execution's attachment witness uses the same labelled source slices as its
position certificate. Witness: zero-error initial success and unique seeded paths.
-/
theorem root_source_attached (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues) (fuel : Nat) (parentType : Name)
    (source : ResolverValue ObjectRef) (selections : List Selection) (state : Nat)
    {result : QueryResult}
    (observed
      : let completed :=
          ((executeRootSelectionSetCore schema resolvers variables
              fuel parentType source selections).run
            state).1
        WorkObservation (selectionSetResultToResponse completed.result) completed.work
          true result)
    (zero : result.totalErrors = 0)
    : let completed :=
        ((executeRootSelectionSetCore schema resolvers variables
            fuel parentType source selections).run
          state).1
      let response := selectionSetResultToResponse completed.result
      WorkAttached (TypedResponse.value [] response.data) completed.work
        (entryPaths
          ((sourceTasks [] none (ResponsePositions.listCursors [] response.data)
              completed.work).map
            SourceTask.entries)) := by
  have success := observed.completionSuccess
    (ExecutionErrors.executeRootSelectionSetCore_positive schema resolvers variables fuel
      parentType source selections state) zero
  obtain ⟨initial, initialEq⟩ := success.1
  obtain ⟨slices, seeded, _⟩ := executeRoot_source_positions schema resolvers variables
    fuel parentType source selections state
  have initialSeed := seeded
  simp only [initialEq, selectionSetResultToResponse,
    GraphQL.Execution.selectionSetResultToResponse, ResponsePositions.listCursors] at initialSeed
  have labelled := sourceTasks_positions initialSeed [] none
  have sourceAttached := (SourceAttachments.executeRoot_seeded_attached schema resolvers
    variables fuel parentType source selections state).2
  have paired :=
    sourceAttached.at (by simpa only [initialEq, resultCursors] using initialSeed)
  simp only [initialEq, TypedResponse.result, List.singleton_append,
    selectionSetResultToResponse, GraphQL.Execution.selectionSetResultToResponse,
    TypedResponse.value, ResponsePositions.listCursors] at paired ⊢
  simpa only [entryPaths, List.map_map, Function.comp_def, SourceTask.entries_paths,
    labelled]
    using paired

/-- The public reconstruction statement holds for arbitrary mixed queries and all
admitted complete schedules/batching. Witness: actual merge preservation, typed source
equivalence to basic execution, unique ordinary positions, and conserved total errors.
-/
theorem mergedExecutionEquivalentToBasic_holds (schema : Schema) (operation : Operation)
    : mergedExecutionEquivalentToBasic schema operation := by
  intro ObjectRef resolvers variables fuel source result observed zero
  have witnessed := queryObservation_workHistory observed
  cases applies : rootSourceAppliesBool schema operation source with
  | false =>
      simp only [applies, Bool.false_eq_true, ↓reduceIte] at witnessed
      subst result
      simp [QueryResult.totalErrors] at zero
  | true =>
      simp only [applies, ↓reduceIte] at witnessed
      obtain ⟨paths, coherent⟩ := Semantics.MixedOwnerPaths.executeRoot_owners schema resolvers
        (coerceVariableValues operation variables) fuel (operation.rootType schema) source
        operation.selectionSet 0
      obtain ⟨slices, seeded, unique⟩ := executeRoot_source_positions schema resolvers
        (coerceVariableValues operation variables) fuel (operation.rootType schema) source
        operation.selectionSet 0
      have attached := root_source_attached schema resolvers (coerceVariableValues operation variables)
        fuel (operation.rootType schema) source operation.selectionSet 0 witnessed zero
      obtain ⟨merged, actual, entries⟩ := witnessed.merge_entries coherent
        (ExecutionErrors.executeRootSelectionSetCore_positive schema resolvers
          (coerceVariableValues operation variables) fuel (operation.rootType schema) source
          operation.selectionSet 0).2 seeded unique attached zero
      obtain ⟨data, basic, inventory⟩ := root_source_entries schema resolvers
        (coerceVariableValues operation variables) fuel (operation.rootType schema) source
        operation.selectionSet 0 witnessed zero
      have response : GraphQL.Execution.executeQueryWithFuel schema resolvers variables
          operation.eraseIncrementalDirectives fuel source = {data := .object data, errors := 0} := by
        have root : GraphQL.Execution.rootSourceAppliesBool schema
            operation.eraseIncrementalDirectives source = true := applies
        simp only [GraphQL.Execution.executeQueryWithFuel, root, ↓reduceIte,
          GraphQL.Execution.executeRootSelectionSet]
        change GraphQL.Execution.selectionSetResultToResponse
          (GraphQL.Execution.executeCollectedFields schema resolvers
            (coerceVariableValues operation variables) fuel (operation.rootType schema) source
            (GraphQL.Execution.collectFields schema (coerceVariableValues operation variables)
              (operation.rootType schema) source
              (SelectionSet.eraseIncrementalDirectives operation.selectionSet))) = _
        rw [basic]
        rfl
      have exactEntries := entries.trans inventory
      have basicUnique : ((TypedResponse.value [] (.object data)).map Prod.fst).Nodup := by
        have unique := BasicPositions.executeQueryWithFuel_nodup schema resolvers variables
          operation.eraseIncrementalDirectives fuel source true
        simpa only [response, TypedResponse.value_paths, source_value_eq_positions] using unique
      refine ⟨merged, actual, ?_⟩
      rw [response]
      exact ⟨
        TypedResponse.value_equivalent [] _ _
          ((exactEntries.map Prod.fst).nodup_iff.mpr basicUnique) basicUnique
          exactEntries,
        (mergeQueryResult_errors result merged actual).trans zero
      ⟩

end GraphQL.IncrementalDelivery.Correctness
