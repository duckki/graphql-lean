import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ItemLineageSafety
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.SuccessfulItemCertificates

/-! Nested item safety shares actual batching, publication, and failure evidence. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

namespace ConformancePlan

/-- Successful source items with item-only producer ancestry are safe under this witness's
historical failure inventory. Streams behind object producers or defer dependencies remain
outside this proved fragment; unrelated deferred work and failures are unrestricted.
-/
def ItemLineagesSafe (work : Execution.Work) (received : List GraphEvent) (w : Witness)
    : Prop :=
  ∀ source index,
    ItemLineage work (.item source index)
    → Occurrence.item source index ∈ received.flatMap GraphEvent.successes
    → ¬TaskCancelled work w.matching w.events w.failures (.item source index)

/-- Nested-item safety restricts to earlier inputs, output prefixes, and fewer cuts.
Witness: any earlier cancellation persists in the larger witness at the same cut.
-/
theorem ItemLineagesSafe.prefix {work received w}
    (safe : ItemLineagesSafe work received w)
    {earlier : List GraphEvent} (prior : earlier.IsPrefix received) (count : Nat)
    {failures : FailureCuts} (included : failures.Subset w.failures)
    : ItemLineagesSafe work earlier
        { w with events := w.events.take count, failures } := by
  intro source index lineage success cancelled
  have observed : Occurrence.item source index ∈ received.flatMap GraphEvent.successes := by
    obtain ⟨event, member, settled⟩ := List.mem_flatMap.mp success
    exact List.mem_flatMap.mpr ⟨event, prior.subset member, settled⟩
  apply safe source index lineage observed
  have atFull := cancelled.append (w.events.drop count)
  rw [List.take_append_drop] at atFull
  exact atFull.mono included

-----------------------------------------------------------------------------------------
-- The common witness now protects arbitrary item-only nesting
-----------------------------------------------------------------------------------------

/-- Actual generated replay has one witness for batching, announced failures, exact fresh
ordered values, and successful item-lineage safety. Witness: specialize the general
successful-item certificate, retaining its matching and merged inventory. This is not
general mixed failure licensing or full output admission.
The actual object/stream cut partitions remain available for mixed boundary proofs.
-/
theorem itemLineageCertificates_with_cuts {work : Execution.Work}
    {inputs : List (List GraphEvent)} (generated : ExecutedWork work)
    (valid : ValidGraphEvents work inputs.flatten)
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
        ∧ ItemLineagesSafe work inputs.flatten w
        ∧ (let queue := initialQueue work
            let publisher : IncrementalPublisher :=
              { active := queue.initialGroups ++ queue.initialStreams }
            let objects :=
              sourceObjectFailureCuts 0
                (queue.eligibleFailureBlocks (queue.sourceRunBlocks publisher inputs).2.2)
            ∃ streams,
              StreamFailureCuts work
                ((queue.runNormalized inputs).2.flatten.flatMap publicationAtoms) streams
              ∧ w.failures = mergeFailureCuts objects streams) := by
  obtain ⟨w, history, shape, announced, values, _, _, safe, partitions⟩ :=
    successfulItemCertificates_with_cuts generated valid started
  exact ⟨w, history, shape, announced, values,
    fun source index _ succeeded => safe source index succeeded, partitions⟩

/-- The common actual witness retains item-lineage safety without exposing its cut split.
Witness: project the partition-retaining construction; existing callers keep the same
interface, while mixed source-boundary proofs can reuse its unchanged object/stream cuts.
-/
theorem itemLineageCertificates {work : Execution.Work} {inputs : List (List GraphEvent)}
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
        ∧ ItemLineagesSafe work inputs.flatten w := by
  obtain ⟨w, history, shape, announced, values, safe, _⟩ :=
    itemLineageCertificates_with_cuts generated valid started
  exact ⟨w, history, shape, announced, values, safe⟩

end ConformancePlan
end GraphQL.IncrementalDelivery.ReferenceWorkQueue
