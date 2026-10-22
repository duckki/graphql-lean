import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ObjectFailureSafety
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.InformativeStreamFailureSafety

/-! Failed stream items are safe before their own cut in the common mixed inventory. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- A ready stream action has already received its structural producer's success.
Witness: invert source readiness and identify the generated stream's unique producer
using its action ref. The item payload is not used to select a producer occurrence.
-/
theorem GraphEvent.Ready.streamProducer_succeeded
    {work stream dependencies producer closing}
    {before : List GraphEvent} {event : GraphEvent}
    (ready : event.Ready work before) (generated : ExecutedWork work)
    (action : event.streamAction = some (stream.ref, closing))
    (known : NodeAt work stream .stream dependencies producer)
    : ∀ source,
        producer = some source → source ∈ before.flatMap GraphEvent.successes := by
  cases event with
  | taskSuccess | taskFailure | groupFailure => cases action
  | streamItems node items =>
      obtain ⟨_, _, _, _, located, _, _, supported, _⟩ := ready
      have refEq := (Prod.mk.inj (Option.some.inj action)).1
      have same := generated.streamProducer_unique (.stream located) known refEq
      intro source produced
      exact supported source (same.trans produced)
  | streamSuccess node | streamFailure node errors =>
      obtain ⟨_, _, _, _, located, supported, _⟩ := ready
      have refEq := (Prod.mk.inj (Option.some.inj action)).1
      have same := generated.streamProducer_unique (.stream located) known refEq
      intro source produced
      exact supported source (same.trans produced)

namespace ConformancePlan

/-- Every failed stream item in `w` is uncancelled under its ordered predecessors.
This is the item-task part of `UncancelledFailures`; the current failure is excluded,
but every earlier cut, including an equal-index object settlement, remains visible.
-/
def StreamFailuresSafe (work : Execution.Work) (w : Witness) : Prop :=
  ∀ before cut address ordinal after,
    w.failures = before ++ (cut, .item address ordinal) :: after
    → ¬TaskCancelled work w.matching (w.events.take cut) before (.item address ordinal)

-----------------------------------------------------------------------------------------
-- Failed actions use their predecessor cuts, not the nonfailure publication theorem
-----------------------------------------------------------------------------------------

/-- General item safety also licenses stream failures on the same ordered inventory.
Witness: the actual failed action recovers its active pre-handler state. Unique stream
closure excludes earlier direct failure; root/item producers are already safe, while
object producers retain a healthy release owner. Visible object cuts align with the
earlier source ledger. The current failing item is never assumed safe or published.
-/
theorem streamFailuresSafe_of_successfulItems {work inputs w streams}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    (announced : AnnouncedFailures work w)
    (safe : SuccessfulItemsSafe work inputs.flatten w)
    (cuts
      : StreamFailureCuts work
          (((initialQueue work).runNormalized inputs).2.flatten.flatMap publicationAtoms)
          streams)
    (exactCuts
      : let queue := initialQueue work
        let publisher : IncrementalPublisher :=
          { active := queue.initialGroups ++ queue.initialStreams }
        w.failures
        = mergeFailureCuts
            (informativeObjectFailureCuts work
              (queue.sourceRunBlocks publisher inputs).2.2)
            streams)
    : StreamFailuresSafe work w := by
  exact informativeStreamFailures_uncancelled generated valid started announced safe cuts exactCuts

end ConformancePlan
end GraphQL.IncrementalDelivery.ReferenceWorkQueue
