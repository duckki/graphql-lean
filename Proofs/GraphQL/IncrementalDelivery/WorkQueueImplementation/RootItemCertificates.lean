import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ItemLineageCertificates

/-! Root-item safety shares the canonical batching and announced-failure witnesses. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

namespace ConformancePlan

/-- Previously successful source items of producer/dependency-free streams are safe under
this witness's full historical inventory. Other streams and deferred work are unrestricted.
This is a proved fragment of item safety, not a new source or public conformance premise.
-/
def RootItemsSafe (work : Execution.Work) (received : List GraphEvent) (w : Witness)
    : Prop :=
  ∀ source index stream result,
    NodeAt work stream .stream [] none
    → TaskAt work (.item source index) [stream.ref] none (.item stream result)
    → Occurrence.item source index ∈ received.flatMap GraphEvent.successes
    → ¬TaskCancelled work w.matching w.events w.failures (.item source index)

/-- Root-item safety restricts to earlier inputs, output prefixes, and fewer failure cuts.
Witness: source successes persist, and any smaller-history cancellation would retain its
original cut in the larger witness. Matching is unchanged; no cut is renumbered.
-/
theorem RootItemsSafe.prefix {work received w} (safe : RootItemsSafe work received w)
    {earlier : List GraphEvent} (prior : earlier.IsPrefix received) (count : Nat)
    {failures : FailureCuts} (included : failures.Subset w.failures)
    : RootItemsSafe work earlier { w with events := w.events.take count, failures } := by
  intro source index stream result root known success cancelled
  have observed : Occurrence.item source index ∈ received.flatMap GraphEvent.successes := by
    obtain ⟨event, member, settled⟩ := List.mem_flatMap.mp success
    exact List.mem_flatMap.mpr ⟨event, prior.subset member, settled⟩
  apply safe source index stream result root known observed
  have atFull := cancelled.append (w.events.drop count)
  rw [List.take_append_drop] at atFull
  exact atFull.mono included

-----------------------------------------------------------------------------------------
-- Root-item safety is constructed on the same history and inventory as the proved leaves
-----------------------------------------------------------------------------------------

/-- Actual generated replay has one witness for batching, announcements, exact fresh
ordered values, and successful root-item safety. Witness: specialize item-lineage safety
to a producer-free item, retaining the same history, matching, and failure inventory.
The original interface is unchanged; object-produced streams remain a separate boundary.
-/
theorem rootItemCertificates {work : Execution.Work} {inputs : List (List GraphEvent)}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    : ∃ w : Witness,
        w.events = (initialQueue work).nonterminalAtoms inputs
        ∧ BatchShape work inputs w
        ∧ AnnouncedFailures work w
        ∧ (∀ index event,
            w.events[index]? = some event
            → IsValue event
            → PublicationAt work (w.matching index) event
              ∧ ¬Published w.matching (w.events.take index) (w.matching index)
              ∧ ∀ address first second,
                  w.matching index = .item address second
                  → first < second
                  → Published w.matching (w.events.take index) (.item address first))
        ∧ RootItemsSafe work inputs.flatten w := by
  obtain ⟨w, history, batching, announced, values, safe⟩ :=
    itemLineageCertificates generated valid started
  refine ⟨w, history, batching, announced, values, ?_⟩
  intro source index stream result root known succeeded
  exact safe source index
    (.step known root (by intro parent impossible; cases impossible)) succeeded

end ConformancePlan
end GraphQL.IncrementalDelivery.ReferenceWorkQueue
