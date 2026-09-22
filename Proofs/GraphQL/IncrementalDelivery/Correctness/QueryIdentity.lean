import Proofs.GraphQL.IncrementalDelivery.Correctness.ResponseReplay
import Proofs.GraphQL.IncrementalDelivery.Correctness.IDUsageProperties

/-! Public identity and finite-run liveness for every conforming observation. -/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution
open MapperIdentity

/-- The proof-only completion uniqueness fact used with causal liveness. -/
def UniqueCompletions : ExecutionObservation → Prop
  | .single _ => True
  | .incremental _ updates => (DeliveryTrace.completedIDs updates).Nodup

/-- Every work observation has unique announcements and completions. Witness: unique
work keys, injective stable allocation, and occurrence-preserving response aggregation.
-/
theorem WorkObservation.uniqueIDs {response work complete result}
    (observed : WorkObservation response work complete result)
    : result.idsUnique ∧ UniqueCompletions result := by
  cases observed with
  | single empty => exact ⟨True.intro, True.intro⟩
  | incremental groups streams batches nonempty batchNonempty admitted finished =>
      have unique := admitted.elim WorkScheduler.AdmissiblePrefix.uniqueKeys
        WorkScheduler.AdmissibleRun.uniqueKeys
      have grouped := replayResponse_groups response groups streams batches
      cases allocated
            : (getPendingEntry (m := StateM IDState) groups streams ensureID).run {} with
      | mk pending ids =>
          rw [allocated] at grouped
          obtain ⟨updates, flatten, replay⟩ := grouped
          have initialKeys := (getPendingEntry_of_eq allocated).2
          have well : Allocated ids := by
            simpa only [allocated]
              using getPendingEntry_allocated groups streams {} .empty
          have finalWell := finalIDs_allocated batches.flatten ids well
          obtain ⟨preserved, completed⟩ := mappedTrace_spec batches.flatten ids
          have announced := (initialKeys.mono preserved).append
            (mappedTrace_pending batches.flatten ids)
          have uniquePending := announced.nodup finalWell unique.1
          have uniqueCompleted := completed.nodup finalWell unique.2
          rw [replay]
          exact ⟨
            by
              simpa only [ExecutionObservation.idsUnique, batched_pendingIDs, flatten]
                using uniquePending,
            by
              simpa only [UniqueCompletions, batched_completedIDs, flatten]
                using uniqueCompleted
          ⟩

/-- In a complete finite work observation every ID completes causally. Witness:
work-key liveness, stable lookup transport, and response-group aggregation.
-/
theorem WorkObservation.idsEventuallyComplete {response work result}
    (observed : WorkObservation response work true result)
    : result.idsEventuallyComplete := by
  cases observed with
  | single empty => trivial
  | incremental groups streams batches nonempty batchNonempty admitted finished =>
      obtain ⟨initialLive, laterLive⟩ := (finished rfl).liveKeys
      have grouped := replayResponse_groups response groups streams batches
      cases allocated
            : (getPendingEntry (m := StateM IDState) groups streams ensureID).run {} with
      | mk pending ids =>
          rw [allocated] at grouped
          obtain ⟨updates, flatten, replay⟩ := grouped
          have initialKeys := (getPendingEntry_of_eq allocated).2
          have live : (ExecutionObservation.incremental
              { toResponse := response, pending, hasNext := true }
              (mappedTrace batches.flatten ids)).idsEventuallyComplete := by
            constructor
            · intro id member
              obtain ⟨key, known, encoded⟩ := initialKeys.fromID id member
              exact mappedTrace_completion encoded (initialLive key known)
            · exact mappedTrace_live ids laterLive
          rw [replay]
          exact batching_idsEventuallyComplete _ _ updates flatten live

/-- Every query prefix has unique wire IDs, by query-to-work observation soundness. -/
theorem deliveryIDsUnique_holds (schema : Schema) (operation : Operation)
    : deliveryIDsUnique schema operation := by
  intro ObjectRef resolvers variables fuel source result observed
  exact queryObservation_property ExecutionObservation.idsUnique
    (fun _ _ _ h => h.uniqueIDs.1) observed

/-- Every complete query outcome closes each announced ID, by finite work liveness.
This asserts no scheduler fairness or eventual host termination.
-/
theorem deliveryIDsEventuallyComplete_holds (schema : Schema) (operation : Operation)
    : deliveryIDsEventuallyComplete schema operation := by
  intro ObjectRef resolvers variables fuel source result observed
  exact queryObservation_property ExecutionObservation.idsEventuallyComplete
    (fun _ _ _ h => h.idsEventuallyComplete) observed

/-- Unique completions plus causal liveness give exactly one completion per announced
ID, by membership and Nodup counts.
-/
theorem idsCompleteExactlyOnce_of_uniqueCompletions_of_liveness
    (result : ExecutionObservation) (unique : UniqueCompletions result)
    (live : result.idsEventuallyComplete)
    : result.idsCompleteExactlyOnce := by
  cases result with
  | single response => trivial
  | incremental initial subsequent =>
      intro id member
      have closed : id ∈ DeliveryTrace.completedIDs subsequent := by
        rcases List.mem_append.mp member with first | later
        · exact live.1 id first
        · exact announcementsEventuallyComplete_pendingIDs subsequent live.2 id later
      change (DeliveryTrace.completedIDs subsequent).Nodup at unique
      simp [unique.count, closed]

/-- Every complete query outcome closes each ID exactly once, combining independently
derived uniqueness and finite-run liveness through the query observation bridge.
-/
theorem deliveryIDsCompleteExactlyOnce_holds (schema : Schema) (operation : Operation)
    : deliveryIDsCompleteExactlyOnce schema operation := by
  intro ObjectRef resolvers variables fuel source result observed
  apply idsCompleteExactlyOnce_of_uniqueCompletions_of_liveness result
  · exact queryObservation_property UniqueCompletions
      (fun _ _ _ h => h.uniqueIDs.2) observed
  · exact deliveryIDsEventuallyComplete_holds schema operation resolvers variables fuel
      source result observed

end GraphQL.IncrementalDelivery.Correctness
