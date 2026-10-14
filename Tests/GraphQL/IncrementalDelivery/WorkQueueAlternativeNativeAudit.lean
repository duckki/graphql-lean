import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.NativeAudit
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.ReceiptPrefixAdmission
import Tests.GraphQL.IncrementalDelivery.Fixtures.HeldSourceCleanup

open GraphQL.IncrementalDelivery.Tests

namespace AlternativeNativeAuditChecks
open GraphQL.IncrementalDelivery
open AlternativeWorkQueue
open AlternativeWorkQueue.NativeRefinement
open WorkQueueSemantics (Occurrence)

private def first : Occurrence := .item [] 0
private def second : Occurrence := .item [] 1
private def receipt : Receipt := .initialize 10 3 [first, second]

private def partialReceipt : Receipt :=
  { receipt with consumed := 1, unwound := true, acknowledged := true }

/-- Finally acknowledges the partially consumed receipt without accepting its suffix. -/
private theorem partial_unwind
    : ReceiptReplay receipt [.consume first, .unwind, .acknowledge] partialReceipt := by
  exact .cons (.consume _ _ rfl rfl)
    (.cons (.unwind _) (.cons (.acknowledge _ rfl rfl) (.nil _)))

example : partialReceipt.accepted = [first] := by rfl

example : partialReceipt.Valid :=
  partial_unwind.preserves_valid (Receipt.initialize_valid _ _ _)

example : ¬ReceiptStep receipt .acknowledge partialReceipt := by
  intro step
  have unwound := step.acknowledge_requires_unwind.1
  contradiction

example : ¬ReceiptStep partialReceipt .acknowledge partialReceipt := by
  intro step
  cases step
  contradiction

example
    : (Receipt.initialize 10 3 []).acknowledgementEffect
      = (Receipt.initialize 11 3 []).acknowledgementEffect := by rfl

example : (Receipt.initialize 10 3 []).id ≠ (Receipt.initialize 11 3 []).id := by decide

private def stream : Execution.DeliveryNode := { ref := 3, path := [] }

private def items : List ReferenceWorkQueue.StreamItem :=
  [
    { occurrence := first, value := { item := .null } },
    { occurrence := second, value := { item := .null } }
  ]

private def sourceResults
    : List (Execution.Result Execution.ResponseValue × Execution.Work) :=
  [(.ok (.null, 0), .empty), (.ok (.null, 0), .empty)]

private def sourceWork : Execution.Work := .stream stream sourceResults

private theorem sourceMatching
    : ReferenceWorkQueue.GraphEvent.MatchesWork sourceWork
        (.streamItems stream items) := by
  intro item selected
  simp only [items, List.mem_cons, List.not_mem_nil, or_false] at selected
  rcases selected with firstItem | secondItem
  · subst item
    refine ⟨[3], none, ?_, rfl⟩
    exact ⟨stream, sourceResults, [], .ok (.null, 0), .empty, rfl, rfl, rfl, rfl⟩
  · subst item
    refine ⟨[3], none, ?_, rfl⟩
    exact ⟨stream, sourceResults, [], .ok (.null, 0), .empty, rfl, rfl, rfl, rfl⟩

private theorem fresh
    : ReferenceWorkQueue.GraphEvent.Fresh [] (.streamItems stream items) := by
  simp [ReferenceWorkQueue.GraphEvent.Fresh, ReferenceWorkQueue.GraphEvent.identities, items, first, second]

private theorem ready
    : ReferenceWorkQueue.GraphEvent.Ready sourceWork [] (.streamItems stream items) := by
  refine ⟨[], sourceResults, none, [], rfl, ?_, ?_, ?_, rfl⟩
  · decide
  · simp
  · intro source impossible
    cases impossible

-- A partially unwound receipt licenses only its first item, with the original source laws.
example
    : graphEffects { rootStreams := [3] }
        (.streamItems stream (items.take partialReceipt.consumed))
      = [.adopt first, .acknowledge 3] :=
  (ReceiptReplay.prefix_graphEffects (stream := stream) (items := items) partial_unwind
    rfl rfl).1

example
    : ReferenceWorkQueue.ValidGraphEvents sourceWork
        [.streamItems stream (items.take 1)] :=
  (ReceiptReplay.prefix_sourceAdmission (stream := stream) (items := items)
    partial_unwind .nil sourceMatching fresh ready (by decide)).1

-- Keeping the unconsumed suffix would falsely announce a second adoption.
example
    : graphEffects { rootStreams := [3] } (.streamItems stream items)
      ≠ [.adopt first, .acknowledge 3] := by
  intro same
  have lengths := congrArg List.length same
  contradiction

example
    : ¬ReferenceWorkQueue.GraphEvent.Ready sourceWork []
        (.streamItems stream (items.take 0)) :=
  streamItems_empty_not_ready _ _ _

private def requested : ResourceState :=
  HeldSourceCleanup.leases.set (.stream 3) (.cleanupRequested .queue)

private def released : ResourceState := requested.set (.stream 3) .released

private theorem disposal
    : ResourceReplay HeldSourceCleanup.leases
        [.requestCleanup (.stream 3), .settleCleanup (.stream 3)] released := by
  exact .cons (.request HeldSourceCleanup.leases (.stream 3) .queue HeldSourceCleanup.owned)
    (.cons (.settle requested (.stream 3) .queue rfl) (.nil _))

example : released (.stream 3) = .released := by simp [released, ResourceState.set]

example : released (.stream 3) ≠ .unacquired :=
  disposal.never_forgets _ (by rw [HeldSourceCleanup.owned]; simp)

example : ¬ResourceStep requested (.requestCleanup (.stream 3)) released := by
  intro step
  obtain ⟨owner, owned⟩ := step.request_requires_owned
  simp [requested, ResourceState.set] at owned

private def prompt : CleanupTracker := { pending := [7], responseFinished := true }

private def notified : CleanupTracker :=
  { responseFinished := true, asyncWorkFinished := true }

/-- Response closure does not seal tracking; a later cleanup registration is legal. -/
private theorem tracked_cleanup
    : CleanupReplay {}
        [
          .register 7,
          .responseFinished,
          .register 8,
          .settle 7,
          .settle 8,
          .asyncWorkFinished
        ]
        notified := by
  exact .cons (.register _ _ (by simp) rfl)
    (.cons (.responseFinished _ rfl)
      (.cons (.register _ _ (by decide) rfl)
        (.cons (.settle _ _ (by decide))
          (.cons (.settle _ _ (by decide))
            (.cons (.asyncWorkFinished _ rfl rfl rfl) (.nil _))))))

example : notified.Valid := tracked_cleanup.preserves_valid CleanupTracker.empty_valid

example : ¬CleanupStep prompt .asyncWorkFinished notified := by
  intro step
  have empty := step.asyncFinish_requires_settlement.2
  contradiction

example : CleanupStep { pending := [7] } .responseFinished prompt :=
  .responseFinished _ rfl

example : ¬CleanupStep notified (.register 9) notified := by
  intro step
  cases step

-- The health counterexample, corrected disposal regression, and reduction target are checked.
example : ¬SafeParentCuts orphanedChild := orphanedChild_cuts_unsafe

example : StopCoverage HeldSourceCleanup.failed.state HeldSourceCleanup.requested :=
  HeldSourceCleanup.final_coverage

example (audit : AuditWitness) : audit.Valid → audit.LocalSafety := audit.localSafety

#print axioms AuditWitness.localSafety
#print axioms groupIsHealthy_eq_reference
#print axioms HeldSourceCleanup.disposal
#print axioms HeldSourceCleanup.failure_effects
#print axioms ReceiptReplay.initialized_prefix
#print axioms ReceiptReplay.full_graphEffects
#print axioms ReceiptReplay.prefix_graphEffects
#print axioms ReceiptReplay.prefix_sourceAdmission
#print axioms validGraphEvents_append_streamPrefix
#print axioms ReceiptReplay.acknowledgementCount_le_one
#print axioms ResourceReplay.never_forgets
#print axioms CleanupReplay.preserves_valid
#print axioms CleanupReplay.asyncFinishCount_le_one
#print axioms partial_unwind
#print axioms disposal
#print axioms tracked_cleanup

end AlternativeNativeAuditChecks
