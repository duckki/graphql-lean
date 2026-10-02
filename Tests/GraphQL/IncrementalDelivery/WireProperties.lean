import Proofs.GraphQL.IncrementalDelivery.Correctness
import Tests.GraphQL.IncrementalDelivery.Correctness

/-! Proof-interface regressions for wire properties, independent of scheduler realization. -/

namespace GraphQL.IncrementalDelivery.Tests.WireProperties

open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Tests.Correctness

/-- Safety implies unique announcements and causal references, using the checked wire
witnesses.
-/
example (result : ExecutionObservation) (safe : result.idUsageValid)
    : result.idsUnique ∧ result.patchesAnnounced :=
  ⟨idsUnique_of_idUsageValid result safe, patchesAnnounced_of_idUsageValid result safe⟩

/-- The complete checker supplies safety, causal liveness, and exactly-once completion. -/
example (result : ExecutionObservation) (complete : result.lifecycleValid = true)
    : result.idUsageValid
      ∧ result.idsEventuallyComplete
      ∧ result.idsCompleteExactlyOnce :=
  ⟨
    idUsageValid_of_lifecycleValid result complete,
    idsEventuallyComplete_of_lifecycleValid result complete,
    idsCompleteExactlyOnce_of_lifecycleValid result complete
  ⟩

/-- Public exactly-once composition still requires independent safety and liveness
witnesses.
-/
example (schema : Schema) (operation : Operation)
    (safe : deliveryIDUsageValid schema operation)
    (live : deliveryIDsEventuallyComplete schema operation)
    : deliveryIDsCompleteExactlyOnce schema operation :=
  deliveryIDsCompleteExactlyOnce_of_idUsageValid_of_liveness schema operation safe live

/-- Lifecycle decomposes into safety and the independent closure/continuation obligations.
-/
example (result : ExecutionObservation)
    : result.lifecycleValid = true ↔ result.idUsageValid ∧ QueryControl result :=
  lifecycleValid_iff_idUsageValid_control result

/-- Same-update announcements, patches, and completions satisfy the general exactly-once
theorem.
-/
example : sameUpdateNotice.idsCompleteExactlyOnce :=
  idsCompleteExactlyOnce_of_lifecycleValid sameUpdateNotice (by decide)

/-- IDs may close before the final response; the checker still supplies full control and
liveness.
-/
example
    : QueryControl separatedTermination ∧ separatedTermination.idsEventuallyComplete :=
  ⟨
    (lifecycleValid_iff_idUsageValid_control separatedTermination).mp (by decide) |>.2,
    idsEventuallyComplete_of_lifecycleValid separatedTermination (by decide)
  ⟩

def badContinuation : ExecutionObservation :=
  .incremental
    { data := .object [], pending := [{ id := "d", path := [] }], hasNext := true }
    [{ hasNext := true, completed := [{ id := "d" }] }]

/-- Safe, live IDs still complete exactly once when the last hasNext flag is wrong. -/
example : badContinuation.idsCompleteExactlyOnce := by
  apply idsCompleteExactlyOnce_of_idUsageValid_of_liveness
  · simp [badContinuation, ExecutionObservation.idUsageValid, DeliveryTrace.idUsageValid]
  · simp [badContinuation, ExecutionObservation.idsEventuallyComplete,
      DeliveryTrace.completedIDs, DeliveryTrace.announcementsEventuallyComplete]

#guard !badContinuation.lifecycleValid

def completionBeforeAnnouncement : ExecutionObservation :=
  .incremental
    { data := .object [], pending := [{ id := "d", path := [] }], hasNext := true }
    [
      { hasNext := true, completed := [{ id := "late" }] },
      {
        hasNext := false,
        pending := [{ id := "late", path := [] }],
        completed := [{ id := "d" }]
      }
    ]

/-- Global closure without safety does not imply causal liveness; unfold the two update
suffixes.
-/
example
    : completionBeforeAnnouncement.idsCompleteExactlyOnce
      ∧ ¬completionBeforeAnnouncement.idsEventuallyComplete := by
  simp [completionBeforeAnnouncement, ExecutionObservation.idsCompleteExactlyOnce,
    ExecutionObservation.idsEventuallyComplete, DeliveryTrace.pendingIDs, DeliveryTrace.completedIDs,
    DeliveryTrace.announcementsEventuallyComplete]

#guard !completionBeforeAnnouncement.lifecycleValid

/-- Successful reconstruction inherits the checker's lifecycle and exactly-once
guarantees.
-/
example (result : ExecutionObservation) (response : Response)
    (merged : mergeExecutionObservation result = some response)
    : result.lifecycleValid = true ∧ result.idsCompleteExactlyOnce :=
  ⟨
    lifecycleValid_of_mergeExecutionObservation result response merged,
    idsCompleteExactlyOnce_of_mergeExecutionObservation result response merged
  ⟩

/-- Reconstruction preserves initial, payload, and completion error counts, using the
general theorem.
-/
example (response : Response)
    (merged : mergeExecutionObservation errorEnvelopes = some response)
    : response.errors = 31 :=
  (mergeExecutionObservation_errors errorEnvelopes response merged).trans (by rfl)

/-- Lifecycle validity alone does not guarantee a merge; the missing attachment point is
unchanged.
-/
example
    : missingParent.idsCompleteExactlyOnce
      ∧ mergeExecutionObservation missingParent = none :=
  ⟨idsCompleteExactlyOnce_of_lifecycleValid missingParent (by decide), rfl⟩

end GraphQL.IncrementalDelivery.Tests.WireProperties
