import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.NativeHealth
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.ResourceOwnership
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.ReceiptLifecycle
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.CleanupSettlement

/-! Shared audit evidence and a checked reduction to local safety. Constructing this
evidence from actual native execution remains open. In particular, Valid is not a new
EventSource premise and does not certify correspondence of two independently chosen traces.
-/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement

/-- One audit witness holds the queue boundary and all three protocol histories together.
Receipt/source callback identities and tracker tokens are ghost names, not runtime storage.
-/
structure AuditWitness where
  queue : State
  resourcesBefore : ResourceState
  resourceActions : List ResourceAction
  resourcesAfter : ResourceState
  receiptBefore : Receipt
  receiptActions : List ReceiptAction
  receiptAfter : Receipt
  cleanupBefore : CleanupTracker
  cleanupActions : List CleanupAction
  cleanupAfter : CleanupTracker

/-- Required evidence at one audit boundary. The actual code-to-observation mapping must
establish every field for the same run, including completeness of resource/tracker inventories.
-/
def AuditWitness.Valid (audit : AuditWitness) : Prop :=
  SafeParentCuts audit.queue.queue
  ∧ StopCoverage audit.queue audit.resourcesAfter
  ∧ ResourceReplay audit.resourcesBefore audit.resourceActions audit.resourcesAfter
  ∧ audit.receiptBefore.Valid
  ∧ ReceiptReplay audit.receiptBefore audit.receiptActions audit.receiptAfter
  ∧ audit.cleanupBefore.Valid
  ∧ CleanupReplay audit.cleanupBefore audit.cleanupActions audit.cleanupAfter

def AuditWitness.LocalSafety (audit : AuditWitness) : Prop :=
  (∀ key, groupIsHealthy audit.queue.queue key = audit.queue.queue.groupIsHealthy key)
  ∧ (∀ target,
      audit.resourcesBefore target ≠ .unacquired
      → audit.resourcesAfter target ≠ .unacquired)
  ∧ (audit.queue.stopped = false
      → ∀ target,
          audit.resourcesAfter target = .owned .queue
          → target ∈ audit.queue.cancel.2.filterMap HostEffect.cleanupStart?)
  ∧ audit.receiptAfter.Valid
  ∧ audit.receiptAfter.accepted
    = audit.receiptBefore.accepted
      ++ audit.receiptActions.filterMap ReceiptAction.consumed?
  ∧ audit.receiptActions.countP ReceiptAction.isAcknowledgement ≤ 1
  ∧ audit.cleanupAfter.Valid
  ∧ audit.cleanupActions.countP CleanupAction.isResponseFinished ≤ 1
  ∧ audit.cleanupActions.countP CleanupAction.isAsyncWorkFinished ≤ 1

/-- Checked local reduction only: no claim that native execution constructs Valid evidence. -/
theorem AuditWitness.localSafety (audit : AuditWitness) (valid : audit.Valid)
    : audit.LocalSafety := by
  obtain ⟨cuts, covered, resources, receiptValid, receipt, cleanupValid, cleanup⟩ := valid
  exact ⟨groupIsHealthy_eq_reference _ cuts, resources.never_forgets,
    fun running target owned => cancel_requests_owned _ _ running covered target owned,
    receipt.preserves_valid receiptValid, receipt.accepted,
    receipt.acknowledgementCount_le_one, cleanup.preserves_valid cleanupValid,
    cleanup.responseFinishCount_le_one, cleanup.asyncFinishCount_le_one⟩

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
