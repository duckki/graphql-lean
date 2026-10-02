import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ActiveObjectStreamHealth
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ItemLineageCertificates

/-! Mixed object-stream boundary health uses the canonical conformance witness. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

namespace ConformancePlan

/-- Each object-produced stream's nonfailure action is safe once earlier source items are.
`inputs` retains real host batching; `w` supplies the common output, matching, and cuts.
The recovered source prefix ends before this action's handler, excluding its own items.
This is a proved conditional bridge for the remaining induction, not a scheduler premise.
-/
def ObjectStreamBoundariesSafe (work : Execution.Work) (inputs : List (List GraphEvent))
    (w : Witness)
    : Prop :=
  ∀ index event stream dependencies source closing,
    w.events[index]? = some event
    → NodeAt work stream .stream dependencies (some (.executionGroup source))
    → streamAction event = some (stream.key, closing)
    → (∀ node errors, event ≠ .streamFailure node errors)
    → ∃ before input after,
        inputs.flatten = before ++ input :: after
        ∧ input.streamAction = some (stream.key, closing)
        ∧ ((∀ address ordinal,
              Occurrence.item address ordinal ∈ before.flatMap GraphEvent.successes
              → ¬TaskCancelled work w.matching (w.events.take index) w.failures
                  (.item address ordinal))
            → ¬TaskCancelled work w.matching (w.events.take index) w.failures
                (.executionGroup source)
              ∧ ¬NodeFailed work w.matching (w.events.take index) w.failures stream.key)

/-- One actual witness has batching, announced failures, item-lineage safety, and the
object-stream boundary bridge. Witness: retain the original construction's cut partitions,
apply actual pre-handler alignment, and remove only its optional terminal suffix. Earlier
source-item safety is still the explicit induction obligation; no cut or trace is replaced.
-/
theorem objectStreamBoundaryCertificates {work : Execution.Work}
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
        ∧ ObjectStreamBoundariesSafe work inputs w := by
  obtain ⟨w, history, shape, announced, values, lineages, streams, cuts, inventory⟩ :=
    itemLineageCertificates_with_cuts generated valid started
  refine ⟨w, history, shape, announced, values, lineages, ?_⟩
  intro index event stream dependencies source closing selected known action nonfailure
  have terminalShape := (initialQueue work).runNormalized_terminalShape inputs
    (createWorkQueue_terminated _)
  have bound := (List.getElem?_eq_some_iff.mp selected).1
  have atFull
      : (((initialQueue work).runNormalized inputs).2.flatten.flatMap publicationAtoms)[index]?
        = some event := by
    rw [terminalShape, ← history, List.getElem?_append_left bound]
    exact selected
  have before : (((initialQueue work).runNormalized inputs).2.flatten.flatMap
      publicationAtoms).take index = w.events.take index := by
    rw [terminalShape, ← history, List.take_append_of_le_length (Nat.le_of_lt bound)]
  have partition := inventory ▸ mergeFailureCuts_partition
    (sourceObjectFailureCuts 0
      ((initialQueue work).eligibleFailureBlocks
        ((initialQueue work).sourceRunBlocks
          { active := (initialQueue work).initialGroups ++ (initialQueue work).initialStreams }
          inputs).2.2)) streams
  obtain ⟨prior, input, after, split, action, _, bridge⟩ :=
    generated.atomicObjectStreamHealthy_of_earlierItems valid started cuts
    partition known atFull action nonfailure (matching := w.matching)
  exact ⟨prior, input, after, split, action, by simpa only [before] using bridge⟩

end ConformancePlan
end GraphQL.IncrementalDelivery.ReferenceWorkQueue
