import Proofs.GraphQL.IncrementalDelivery.Correctness.FailureScopeMapping
import Proofs.GraphQL.IncrementalDelivery.Correctness.SourcePublicationCoverage
import Proofs.GraphQL.IncrementalDelivery.Correctness.SourceTypedEntries

/-! Errored complete observations address their prepared successful source positions.
Ordinary execution's null bubbling is a separate response-reconstruction boundary.
-/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution
open WorkQueueSemantics
open Semantics.MixedPaths

-----------------------------------------------------------------------------------------
-- Successful source payloads stay below their task attachment
-----------------------------------------------------------------------------------------

/-- Every source position lies at or below the task's attachment path.
Witness: typed field entries lie below a field, and item entries below their absolute
item index; both extend the enclosing object or stream attachment.
-/
theorem SourceTask.positions_below_attachment (task : SourceTask) (containers : Bool)
    {path : ResponsePath} (member : path ∈ task.positions containers)
    : task.payload.path.IsPrefix path := by
  rw [← task.entries_positions containers] at member
  obtain ⟨entry, present, projected⟩ := List.mem_filterMap.mp member
  have same : entry.1 = path := by
    rcases entry with ⟨root, atom⟩
    cases atom <;> cases containers <;> simp_all [TypedResponse.entryPath]
  have below : Semantics.Below task.payload.path entry.1 := by
    cases payload : task.payload with
    | object root result =>
        cases result with
        | error errors =>
            simp [SourceTask.entries, payload, TypedResponse.result] at present
        | ok pair =>
            have located : entry ∈ TypedResponse.fields root pair.1 := by
              simpa only [SourceTask.entries, payload, TypedResponse.result] using present
            exact Semantics.underFields_below
              (TypedResponse.fields_under root pair.1 entry located)
    | item node result =>
        cases result with
        | error errors =>
            simp [SourceTask.entries, payload, TypedResponse.result] at present
        | ok pair =>
            have located : entry ∈ TypedResponse.value (node.path ++ [.index task.index])
                pair.1 := by
              simpa only [SourceTask.entries, payload, TypedResponse.result] using present
            exact Semantics.below_child (TypedResponse.value_below _ pair.1 entry located)
  obtain ⟨suffix, equal⟩ := below
  exact ⟨suffix, (same ▸ equal).symm⟩

-----------------------------------------------------------------------------------------
-- Published source positions are delivered; unpublished source positions are reported
-----------------------------------------------------------------------------------------

/-- An arbitrary complete replay addresses its initial and successful source positions,
including executions with later errors. Witness: exact publication decoding delivers
published labels, and terminal reports cover every position of unpublished labels.
This is source coverage, not yet equivalence to ordinary directive-erased execution.
-/
theorem replayResponse_source_addressed
    {paths bound response work groups streams batches sourceSlices scopes}
    (coherent : Semantics.MixedOwnerPaths.WorkAt paths bound work)
    (seeded
      : WorkCursorSeed (ResponsePositions.listCursors [] response.data) work sourceSlices)
    (source
      : (ResponsePositions.value true [] response.data ++ sourceSlices.flatten).Nodup)
    (run : AdmissibleRun work ⟨groups, streams, batches.flatten⟩)
    (safe : (replayResponse response groups streams batches).idUsageValid)
    (decodedScopes
      : (replayResponse response groups streams batches).collectFailureScopes
        = some scopes)
    (containers : Bool)
    : ∃ slices,
        (replayResponse response groups streams batches).DeliversSlices containers slices
        ∧ ∀ path ∈
            ResponsePositions.value containers [] response.data
            ++ (sourceTasks [] none (ResponsePositions.listCursors [] response.data)
                  work).flatMap
                (SourceTask.positions containers),
            path ∈ slices.flatten ∨ ∃ scope ∈ scopes, scope.IsPrefix path := by
  obtain ⟨events, matching, failures, explained, terminal, batching⟩ := run
  have initialHistory : CursorHistory (ResponsePositions.listCursors [] response.data)
      (ResponsePositions.value true [] response.data) := by
    simpa only [source_value_eq_positions] using listCursors_positions [] response.data
  have sourceUnique : (ResponsePositions.value true [] response.data
      ++ (sourceTasks [] none (ResponsePositions.listCursors [] response.data) work).flatMap
        (SourceTask.positions true)).Nodup := by
    simpa only [List.flatMap, sourceTasks_positions seeded] using source
  have exactDecode := decode_historyPositionAtoms (containers := containers)
    explained seeded initialHistory sourceUnique events.length (Nat.le_refl _)
  have nodePaths : ∀ node ∈ (events ++ [WorkQueueEvent.workQueueTermination]).flatMap eventNodes,
      paths node.ref = node.path := by
    intro node member
    simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, eventNodes,
      List.append_nil] at member
    obtain ⟨kind, dependencies, birth, known⟩ := explained_nodes explained node member
    exact (workAt_node coherent known).2
  have atoms := workBatching_positionAtoms batching nodePaths
  have decoded : decodeAtoms containers (ResponsePositions.listCursors [] response.data)
      (batches.flatten.flatten.flatMap eventPositionAtoms)
      = some
          ((sourcePrefixTasks (sourceTasks [] none (ResponsePositions.listCursors [] response.data)
              work) matching events events.length).flatMap (SourceTask.positions containers),
            sourceHistoryCursors (sourceTasks [] none (ResponsePositions.listCursors [] response.data)
              work) matching events (ResponsePositions.listCursors [] response.data) events.length) := by
    rw [atoms]
    simpa only [List.take_length, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      eventPositionAtoms, List.append_nil] using exactDecode
  obtain ⟨slices, delivered, flattened⟩ := replayResponse_positions coherent
    (Or.inr ⟨events, matching, failures, explained, terminal, batching⟩) safe decoded
  refine ⟨slices, delivered, ?_⟩
  intro path member
  rcases List.mem_append.mp member with initial | future
  · exact Or.inl (flattened ▸ List.mem_append_left _ initial)
  · obtain ⟨task, present, selected⟩ := List.mem_flatMap.mp future
    obtain ⟨owners, known⟩ := sourceTasks_known .root _ present
    by_cases published : Published matching events task.occurrence
    · obtain ⟨index, event, atIndex, value, same⟩ := published
      have included := sourcePrefixTasks_of_publication present atIndex value same.symm
        (List.getElem?_eq_some_iff.mp atIndex).1
      exact Or.inl (flattened ▸ List.mem_append_right _
        (List.mem_flatMap.mpr ⟨task, included, selected⟩))
    · obtain ⟨scope, member, below⟩ := replayResponse_unpublishedScope coherent explained
        terminal batching decodedScopes known published
      exact Or.inr ⟨scope, member, below.trans (task.positions_below_attachment containers selected)⟩

/-- Every complete work observation addresses all positions of its prepared successful
payloads. Witness: ordinary work has no future tasks; incremental work supplies a terminal
history, total scope decoding, and partial source coverage even with counted errors.
-/
theorem WorkObservation.source_addressed
    {paths bound response work result sourceSlices}
    (observed : WorkObservation response work true result)
    (coherent : Semantics.MixedOwnerPaths.WorkAt paths bound work)
    (seeded
      : WorkCursorSeed (ResponsePositions.listCursors [] response.data) work sourceSlices)
    (source
      : (ResponsePositions.value true [] response.data ++ sourceSlices.flatten).Nodup)
    (containers : Bool)
    : ∃ slices scopes,
        result.DeliversSlices containers slices
        ∧ result.collectFailureScopes = some scopes
        ∧ ∀ path ∈
            ResponsePositions.value containers [] response.data
            ++ (sourceTasks [] none (ResponsePositions.listCursors [] response.data)
                  work).flatMap
                (SourceTask.positions containers),
            path ∈ slices.flatten ∨ ∃ scope ∈ scopes, scope.IsPrefix path := by
  have safe := observed.idUsageValid
  obtain ⟨scopes, decoded⟩ := ExecutionObservation.failureScopes_exist safe
  cases observed with
  | single empty =>
      have noTasks : sourceTasks [] none (ResponsePositions.listCursors [] response.data)
          work = [] := by
        apply List.eq_nil_iff_forall_not_mem.mpr
        intro task member
        obtain ⟨owners, known⟩ := sourceTasks_known .root _ member
        exact no_tasks_of_size_zero empty known
      refine ⟨
        [ResponsePositions.value containers [] response.data],
        scopes,
        rfl,
        decoded,
        ?_
      ⟩
      intro path member
      exact Or.inl
        (by simpa only [noTasks, List.flatMap_nil, List.append_nil,
          List.flatten_cons, List.flatten_nil] using member)
  | incremental groups streams batches _ _ _ finished =>
      obtain ⟨slices, delivered, addressed⟩ := replayResponse_source_addressed coherent
        seeded source (finished rfl) safe decoded containers
      exact ⟨slices, scopes, delivered, decoded, addressed⟩

end GraphQL.IncrementalDelivery.Correctness
