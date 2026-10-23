import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupGroupClosureMetadata
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupStreamAnnouncements
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupStreamNoticeMetadata
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupStreamSourceOrder
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamOpenness

/-! Every actual startup stream reference uses an announced, uncompleted ref. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Initial or earlier stream notices supply structural metadata for every stream reference. -/
theorem State.startup_runNormalized_streamReference_refLocated {work : Execution.Work}
    (startup : InitialStartup) {batches : List (List GraphEvent)}
    (valid : ValidGraphEvents work batches.flatten) {index : Nat} {event ref}
    (atEvent
      : ((((State.initialize (Work.fromExecution work) startup)).runNormalized
            batches).2.flatten.flatMap
          publicationAtoms)[index]?
        = some event)
    (reference : ref ∈ streamReferenceRefs event)
    : ∃ stream dependencies producer,
        stream.ref = ref ∧ NodeAt work stream .stream dependencies producer := by
  have noticed := (State.startup_runNormalized_atomicStreamReferences startup valid).atEvent
    atEvent reference
  rcases List.mem_append.mp noticed with initial | earlier
  · rw [State.initializeWithStartup_initialStreams] at initial
    obtain ⟨stream, member, same⟩ := List.mem_map.mp initial
    exact ⟨stream, [], none, same, (createWorkQueue_initialStreams_nodeAt work).2 stream member⟩
  · obtain ⟨carrier, member, streamRef⟩ := List.mem_flatMap.mp earlier
    have metadata := State.startup_runNormalized_atomicStreamNoticesLocated startup valid carrier
      (List.mem_of_mem_take member)
    obtain ⟨stream, same, dependencies, producer, known⟩ := metadata.of_ref streamRef
    exact ⟨stream, dependencies, producer, same, known⟩

/-- Every actual startup stream reference is announced and has no earlier same-ref closure.
Source action order excludes stream closures; generated group/stream roles exclude group
closures, including the separately forwarded initial failure tail.
-/
theorem ExecutedWork.startup_runNormalized_streamOpenAt {work : Execution.Work}
    (startup : InitialStartup) {batches : List (List GraphEvent)}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work batches.flatten)
    {index : Nat} {event ref}
    (atEvent
      : ((((State.initialize (Work.fromExecution work) startup)).runNormalized
            batches).2.flatten.flatMap
          publicationAtoms)[index]?
        = some event)
    (reference : ref ∈ streamReferenceRefs event)
    : let queue := (State.initialize (Work.fromExecution work) startup)
      Open ((queue.initialGroups ++ queue.initialStreams).map Execution.DeliveryNode.ref)
        (((queue.runNormalized batches).2.flatten.flatMap publicationAtoms).take index)
        ref := by
  refine ⟨
    State.startup_runNormalized_streamAnnouncedAt startup valid atEvent reference,
    ?_
  ⟩
  obtain ⟨stream, streamDependencies, streamProducer, sameRef, streamKnown⟩ :=
    State.startup_runNormalized_streamReference_refLocated startup valid atEvent reference
  have unclosed := streamActions_ordered_atEvent
    (State.startup_runNormalized_atomicStreamActions_ordered startup valid) atEvent reference
  intro completed
  obtain ⟨prior, member, closed⟩ := List.mem_flatMap.mp completed
  have known := generated.startup_runNormalized_atomicGroupClosuresLocated startup valid prior
    (List.mem_of_mem_take member)
  cases prior with
  | groupSuccess group groups streams | groupFailure group _ =>
      obtain ⟨dependencies, producer, located⟩ := known
      have same := List.mem_singleton.mp closed
      exact generated.groupStreamRefsDisjoint located streamKnown (same.symm.trans sameRef.symm)
  | streamSuccess closedStream | streamFailure closedStream _ =>
      apply unclosed
      have same := List.mem_singleton.mp closed
      exact List.mem_filterMap.mpr ⟨_, member, by simp [streamAction, same]⟩
  | groupValues | streamValues | workQueueTermination => cases closed

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
