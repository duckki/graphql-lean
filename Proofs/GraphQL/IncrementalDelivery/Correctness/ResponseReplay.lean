import Proofs.GraphQL.IncrementalDelivery.Correctness.QueryObservation
import Proofs.GraphQL.IncrementalDelivery.Correctness.MapperAllocation
import Proofs.GraphQL.IncrementalDelivery.Correctness.ResponseBatchLiveness

/-! Finite grouped replay connects the actual response mapper to its induction folds. -/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution
open MapperIdentity

/-- The recursive replay and final-ID helpers are exactly the public batch mapper
traversal; witness: induction on supplied input batches.
-/
theorem mapM_workEvents (batches : List (List WorkEvent)) (ids : IDState)
    : (batches.mapM mapWorkEventBatch).run ids
      = (mappedTrace batches ids, finalIDs batches ids) := by
  induction batches generalizing ids with
  | nil => rfl
  | cons batch rest ih =>
      cases h : mapWorkEventBatch batch ids
      simp [List.mapM_cons, StateT.run, StateT.bind, StateT.pure, bind, pure,
        mappedTrace, finalIDs] at ih ⊢
      simp [h, ih]

/-- Replay the supplied groups while retaining their response boundaries. This is
proof-only input replay, not a selected future of an opaque source.
-/
def replayGroups
    : List (List (List WorkEvent)) → IDState
      → List (List IncrementalStreamUpdateResult) × IDState
  | [], ids => ([], ids)
  | group :: rest, ids =>
      let (updates, middle) := (group.mapM mapWorkEventBatch).run ids
      let (later, final) := replayGroups rest middle
      (updates :: later, final)

/-- Flattening grouped replay is replay of flattened inputs, including the final IDs;
witness: induction using mapM's append equation.
-/
theorem replayGroups_flatten (groups : List (List (List WorkEvent))) (ids : IDState)
    : ((replayGroups groups ids).1.flatten, (replayGroups groups ids).2)
      = (groups.flatten.mapM mapWorkEventBatch).run ids := by
  induction groups generalizing ids with
  | nil => rfl
  | cons group rest ih =>
      cases first : (group.mapM mapWorkEventBatch).run ids with
      | mk updates middle =>
          cases tail : replayGroups rest middle with
          | mk later final =>
              have flat := ih middle
              rw [tail] at flat
              simp only [StateT.run] at first flat
              simp [replayGroups, List.mapM_append, StateT.run,
                StateT.bind, StateT.pure, bind, pure, first, tail, ← flat]

/-- The actual batching mapper combines precisely the groups supplied to replay;
witness: induction through the two nested state traversals.
-/
theorem replayGroups_combined (groups : List (List (List WorkEvent))) (ids : IDState)
    : ((groups.mapM
          fun available => do
            let results ← available.mapM mapWorkEventBatch
            return combineIncrementalResults results)
        : StateM IDState _).run
        ids
      = (
        (replayGroups groups ids).1.map combineIncrementalResults,
        (replayGroups groups ids).2
      ) := by
  induction groups generalizing ids with
  | nil => rfl
  | cons group rest ih =>
      cases first : (group.mapM mapWorkEventBatch) ids
      simp [List.mapM_cons, StateT.run, StateT.bind, StateT.pure, bind, pure,
        replayGroups] at ih ⊢
      simp [first, ih]

/-- Response batching preserves pending-ID occurrences, by aggregation and induction. -/
theorem batched_pendingIDs (batches : List (List IncrementalStreamUpdateResult))
    : DeliveryTrace.pendingIDs (batches.map combineIncrementalResults)
      = DeliveryTrace.pendingIDs batches.flatten := by
  induction batches with
  | nil => rfl
  | cons batch rest ih =>
      change (combineIncrementalResults batch).pending.map IncrementalPendingNotice.id
          ++ DeliveryTrace.pendingIDs (rest.map combineIncrementalResults) = _
      rw [(combineIncrementalResults_ids batch).1, ih]
      simp [DeliveryTrace.pendingIDs, List.flatMap_append]

/-- Replay exposes response groups whose flattening is the stable-ID event replay.
Witness: the grouping equations; no source future or enumeration is used.
-/
theorem replayResponse_groups (response : Response) (initialGroups initialStreams)
    (groups : List (List (List WorkEvent)))
    : let (pending, ids) :=
        (getPendingEntry (m := StateM IDState) initialGroups initialStreams ensureID).run
          {}
      ∃ batches : List (List IncrementalStreamUpdateResult),
        batches.flatten = mappedTrace groups.flatten ids
        ∧ replayResponse response initialGroups initialStreams groups
          = .incremental { toResponse := response, pending, hasNext := true }
              (batches.map combineIncrementalResults) := by
  cases allocated
        : (getPendingEntry (m := StateM IDState)
            initialGroups initialStreams ensureID).run
            {} with
  | mk pending ids =>
      refine ⟨(replayGroups groups ids).1, ?_, ?_⟩
      · exact congrArg Prod.fst
          ((replayGroups_flatten groups ids).trans (mapM_workEvents _ _))
      · simp only [replayResponse, allocated, replayGroups_combined]

end GraphQL.IncrementalDelivery.Correctness
