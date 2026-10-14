import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.NativeAudit
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.GeneratedParentCuts
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.ResourcePrefixConstruction

/-! Derive the audit's queue/resource fields from one actual generated FIFO prefix.
Receipt and cleanup observations remain independent native protocol inputs. Assembling them
does not prove actual callback correspondence or completeness of a native inventory.
-/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement

-----------------------------------------------------------------------------------------
-- Construct audit validity without asking for endpoint coverage or parent safety
-----------------------------------------------------------------------------------------

/-- A constructed resource prefix supplies the audit's parent cuts, stop coverage and legal
history. Equalities bind them to this witness's actual queue and resource fields. Receipt and
tracker histories must independently be legal and refer to the same native run; their callback
correspondence is not inferred from merely placing them in this record.
-/
theorem AuditWitness.valid_of_resourcePrefix (audit : AuditWitness) {work inputs}
    (generated : ReferenceWorkQueue.ExecutedWork work)
    (built
      : ResourcePrefixConstruction work inputs audit.resourcesAfter audit.resourceActions)
    (queue : audit.queue = ((State.initialize work).runNormalized inputs).1)
    (initial : audit.resourcesBefore = ResourceState.empty)
    (receiptValid : audit.receiptBefore.Valid)
    (receipt : ReceiptReplay audit.receiptBefore audit.receiptActions audit.receiptAfter)
    (cleanupValid : audit.cleanupBefore.Valid)
    (cleanup : CleanupReplay audit.cleanupBefore audit.cleanupActions audit.cleanupAfter)
    : audit.Valid := by
  refine ⟨?_, ?_, ?_, receiptValid, receipt, cleanupValid, cleanup⟩
  · rw [queue]
    exact generatedReplay_safeParentCuts generated inputs built.sourceEvidence.1 built.sourceEvidence.2
  · rw [queue]
    exact built.stopCoverage generated
  · rw [initial]
    exact (built.invariants generated).1

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
