import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupClosureAccounting
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupClosureNotices
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamOpenness

/-! Actual group closures refer to announced, uncompleted generated-work refs. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Permanent group retirement and generated role separation exclude earlier closures
-----------------------------------------------------------------------------------------

/-- Every actual atomic group closure refers to an open notice.
Witness: prior-notice accounting supplies announcement; permanent retirement excludes an
earlier group closure, and structural stream provenance plus generated role separation
excludes same-ref stream closures. This does not assume a licensed failure-cut witness.
-/
theorem createWorkQueue_runNormalized_groupClosureOpenAt {work : Execution.Work}
    {batches : List (List GraphEvent)} (generated : ExecutedWork work)
    (valid : ValidGraphEvents work batches.flatten) {index : Nat} {event ref}
    (atEvent
      : (((State.initialize (Work.fromExecution work)).runNormalized
            batches).2.flatten.flatMap
          publicationAtoms)[index]?
        = some event)
    (closure : ref ∈ groupClosureRefs event)
    : let queue := State.initialize (Work.fromExecution work)
      Open ((queue.initialGroups ++ queue.initialStreams).map Execution.DeliveryNode.ref)
        (((queue.runNormalized batches).2.flatten.flatMap publicationAtoms).take index)
        ref := by
  refine ⟨createWorkQueue_runNormalized_groupClosureAnnouncedAt valid atEvent closure, ?_⟩
  have metadata := createWorkQueue_runNormalized_atomicGroupClosuresLocated generated valid _
    (List.mem_of_getElem? atEvent)
  have located : ∃ group dependencies producer,
      group.ref = ref ∧ NodeAt work group .group dependencies producer := by
    cases event with
    | groupSuccess | groupFailure =>
        obtain ⟨dependencies, producer, known⟩ := metadata
        exact ⟨_, dependencies, producer, (List.mem_singleton.mp closure).symm, known⟩
    | groupValues | streamValues | streamSuccess | streamFailure | workQueueTermination =>
        cases closure
  obtain ⟨group, dependencies, producer, same, known⟩ := located
  have unclosed := createWorkQueue_runNormalized_groupUnclosedAt valid atEvent closure
  intro completed
  obtain ⟨prior, member, closed⟩ := List.mem_flatMap.mp completed
  cases prior with
  | groupSuccess closedGroup groups streams | groupFailure closedGroup _ =>
      exact unclosed (List.mem_flatMap.mpr ⟨_, member, closed⟩)
  | streamSuccess closedStream | streamFailure closedStream _ =>
      obtain ⟨priorIndex, atPrior⟩ := List.mem_iff_getElem?.mp (List.mem_of_mem_take member)
      obtain ⟨stream, streamDependencies, streamProducer, sameRef, streamKnown⟩ :=
        createWorkQueue_runNormalized_streamReference_refLocated valid atPrior
          (List.mem_cons_self : closedStream.ref ∈ streamReferenceRefs _)
      exact generated.groupStreamRefsDisjoint known streamKnown
        (same.trans ((List.mem_singleton.mp closed).trans sameRef.symm))
  | groupValues | streamValues | workQueueTermination => cases closed

/-- Failed-group openness is the failure specialization of general closure openness.
Witness: a failed group's own ref is its singleton group-closure projection.
-/
theorem createWorkQueue_runNormalized_groupFailureOpenAt {work : Execution.Work}
    {batches : List (List GraphEvent)} (generated : ExecutedWork work)
    (valid : ValidGraphEvents work batches.flatten) {index : Nat} {group errors}
    (atEvent
      : (((State.initialize (Work.fromExecution work)).runNormalized
            batches).2.flatten.flatMap
          publicationAtoms)[index]?
        = some (.groupFailure group errors))
    : let queue := State.initialize (Work.fromExecution work)
      Open ((queue.initialGroups ++ queue.initialStreams).map Execution.DeliveryNode.ref)
        (((queue.runNormalized batches).2.flatten.flatMap publicationAtoms).take index)
        group.ref :=
  createWorkQueue_runNormalized_groupClosureOpenAt generated valid atEvent
    List.mem_cons_self

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
