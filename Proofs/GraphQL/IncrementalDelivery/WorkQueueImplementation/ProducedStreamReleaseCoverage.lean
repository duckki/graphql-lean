import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.BufferedStreamReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RetiredContributorPublication
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamRegistrationCoverage
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamLoweringCoverage

/-! Healthy contributor retirement forces complete release of an object's child streams. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Exact source storage and child attachment connect to actual notice conservation
-----------------------------------------------------------------------------------------

/-- An object's successful input releases all child streams before healthy owner retirement.
Witness: the finally healthy owner is live at the accepted input; source matching supplies
every child stream, which fresh integration attaches. Replay conservation forces a notice
when the owner retires without cancellation. No publication matching is assumed here.
-/
theorem ExecutedWork.success_retired_childStream_notice
    {work events occurrence result owners producer payload key before after stream
      dependencies}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work events)
    (started : (State.initialize (Work.fromExecution work)).acceptsBatch events = true)
    (known : TaskAt work occurrence owners producer payload) (contributes : key ∈ owners)
    (healthy
      : ¬GroupRecordInvalidated work
          ((State.initialize (Work.fromExecution work)).objectFailureContributions events)
          key)
    (retired
      : ((State.initialize (Work.fromExecution work)).replayGraphEvents
          events).RetiredGroup
          key)
    (uncancelled
      : key
        ∉ ((State.initialize (Work.fromExecution work)).replayGraphEvents
            events).cancelledGroups)
    (sourceEq : events = before ++ .taskSuccess occurrence result :: after)
    (child : NodeAt work stream .stream dependencies (some occurrence))
    : stream.key
      ∈ ((State.initialize (Work.fromExecution work)).rawEventReplay events).2.flatMap
          rawStreamNoticeKeys := by
  obtain ⟨node, found, accepted, owns, live⟩ := generated.success_with_finalHealthyOwner_live
    valid started known contributes healthy sourceEq
  have earlier : before.IsPrefix events := ⟨.taskSuccess occurrence result :: after, sourceEq.symm⟩
  have boundary : (before ++ [GraphEvent.taskSuccess occurrence result]).IsPrefix events :=
    ⟨after, by simp [sourceEq, List.append_assoc]⟩
  obtain ⟨matching, fresh, _⟩ := valid.atPrefix boundary
  obtain ⟨buffered, stored, sameTask, value, attached⟩ :=
    generated.taskSuccess_prepared_childStream (valid.prefix earlier) matching fresh found
      (matching.taskChildStreams_complete child)
  have conserved := generated.success_conservesBufferedStreams (sourceEq ▸ valid)
    (sourceEq ▸ started) found accepted
  have preparedLive := State.maybeIntegrateWork_includesKeys
    (((State.initialize (Work.fromExecution work)).replayGraphEvents before).putTaskNode
      { node with value := some result.value }) result.work (some occurrence) key live
  have finalState : (State.initialize (Work.fromExecution work)).replayGraphEvents events
      = ((State.initialize (Work.fromExecution work)).replayGraphEvents before).replayGraphEvents
        (.taskSuccess occurrence result :: after) := by
    simp only [sourceEq, State.replayGraphEvents, List.foldl_append]
  have noticed := conserved.retired_notice stored value attached (sameTask.symm ▸ owns)
    preparedLive (finalState ▸ retired.2) (finalState ▸ uncancelled)
  rw [sourceEq, State.rawEventReplay_append]
  simp only [State.rawEventReplay_state, List.flatMap_append]
  exact List.mem_append_right _ noticed

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
