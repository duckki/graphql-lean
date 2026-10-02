import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RetiredContributorPublication
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RawPublicationClosures

/-! An already active group has published its healthy ancestors' data before its handler. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Retired source-boundary ancestors have already published their structural contributors
-----------------------------------------------------------------------------------------

/-- A successful already-active group has all ancestor contributions before this handler.
Witness: root ancestry gives prior retirement; this handler's actual successful closure
excludes inherited failure. Healthy-retirement publication applies to the earlier source
prefix on the existing ledger. No completion notice for the ancestor is required.
-/
theorem ExecutedWork.activeAncestorContributor_published_before_handler
    {work before event published group groups streams dependencies key address owners
      producer payload}
    (generated : ExecutedWork work)
    (valid : ValidGraphEvents work (before ++ [event]))
    (started
      : (State.initialize (Work.fromExecution work)).acceptsBatch (before ++ [event])
        = true)
    (covered
      : (State.initialize (Work.fromExecution work)).ReplayClosuresCovered
          (before ++ [event]) published)
    (carrier
      : Execution.WorkQueueEvent.groupSuccess group groups streams
        ∈ (((State.initialize (Work.fromExecution work)).replayGraphEvents
              before).handleGraphEvent
            event).2)
    (active
      : group.key
        ∈ ((State.initialize (Work.fromExecution work)).replayGraphEvents
            before).rootGroups)
    (record : GroupRecordAt work group dependencies) (ancestor : key ∈ dependencies)
    (known : TaskAt work (.executionGroup address) owners producer payload)
    (contributes : key ∈ owners)
    : ∃ value,
        (Occurrence.executionGroup address, value)
        ∈ published.take
            (((State.initialize (Work.fromExecution work)).rawEventReplay
                before).2.flatMap
              WorkQueueEvent.objectValues).length := by
  have prior := valid.prefix (List.prefix_append before [event])
  have accepted := State.acceptsBatch_prefix started
  have roots := (generated.replayGraphEvents_structuralRetirement before
    (fun _ member => prior.eachMatches member)).1
  have retired := roots group.key active group dependencies record rfl key ancestor
    (.executionGroup address) owners ⟨producer, payload, known⟩ contributes
  obtain ⟨_, _, _, healthy, _⟩ :=
    generated.replayGraphEvents_successfulCarrier_retiredHealthy valid accepted carrier
  have ownerHealthy : ¬GroupRecordInvalidated work
      ((State.initialize (Work.fromExecution work)).objectFailureContributions before) key := by
    intro invalid
    apply healthy
    apply GroupRecordInvalidated.ancestor record ancestor
    apply invalid.mono
    rw [State.objectFailureContributions_append]
    exact List.subset_append_right _ _
  exact generated.retired_structuralContributor_published prior accepted
    (covered.prefix before [event]) known contributes retired ownerHealthy

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
