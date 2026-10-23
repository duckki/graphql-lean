import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.InitialStartupReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamPublication

/-! Ordinary startup replay preserves every accepted stream item in source order. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Startup source items have exact occurrence-unique witnesses in the actual output. -/
theorem State.startup_runNormalized_itemSources {work : Execution.Work}
    (startup : InitialStartup) {batches : List (List GraphEvent)}
    (valid : ValidGraphEvents work batches.flatten)
    (started : inputsStarted work batches startup = true)
    : let initial := State.initialize (Work.fromExecution work) startup
      let publications := batches.flatten.flatMap GraphEvent.itemPublications
      (publications.map Prod.fst).Nodup
      ∧ publications.map Prod.snd
        = (initial.runNormalized batches).2.flatten.flatMap normalizedItemValues
      ∧ ∀ publication ∈ publications,
          ∃ owners producer,
            TaskAt work publication.1 owners producer
              (.item publication.2.1
                (.ok (publication.2.2.item, publication.2.2.errors))) := by
  refine ⟨
    (GraphEvent.itemPublications_sublist _).nodup valid.identities_nodup.1,
    (State.runNormalized_itemValues _ _ valid
      (by rwa [← inputsStartedWithStartup_eq_batchesStarted])).symm,
    ?_
  ⟩
  intro publication member
  obtain ⟨event, eventMember, itemMember⟩ := List.mem_flatMap.mp member
  exact (valid.event_matches eventMember).itemPublications itemMember

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
