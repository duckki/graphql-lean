import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupGroupClosureNotices
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupGroupClosureAccounting
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupStreamOpenness

/-! Actual startup group completions use announced, uncompleted refs. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Prior notices, permanent retirement and generated group/stream role separation make
 every actual startup group completion open, including a delayed initial failure report.
-/
theorem ExecutedWork.startup_runNormalized_groupClosureOpenAt {work : Execution.Work}
    (startup : InitialStartup) {batches : List (List GraphEvent)}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work batches.flatten)
    (started : inputsStarted work batches startup = true) {index : Nat} {event ref}
    (atEvent
      : ((((State.initialize (Work.fromExecution work) startup)).runNormalized
            batches).2.flatten.flatMap
          publicationAtoms)[index]?
        = some event)
    (closure : ref ∈ groupClosureRefs event)
    : let queue := (State.initialize (Work.fromExecution work) startup)
      Open ((queue.initialGroups ++ queue.initialStreams).map Execution.DeliveryNode.ref)
        (((queue.runNormalized batches).2.flatten.flatMap publicationAtoms).take index)
        ref := by
  refine ⟨
    State.startup_runNormalized_groupClosureAnnouncedAt startup valid atEvent closure,
    ?_
  ⟩
  have metadata := generated.startup_runNormalized_atomicGroupClosuresLocated startup valid _
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
  have unclosed := State.startup_runNormalized_groupUnclosedAt startup valid started atEvent closure
  intro completed
  obtain ⟨prior, member, closed⟩ := List.mem_flatMap.mp completed
  cases prior with
  | groupSuccess closedGroup groups streams | groupFailure closedGroup _ =>
      exact unclosed (List.mem_flatMap.mpr ⟨_, member, closed⟩)
  | streamSuccess closedStream | streamFailure closedStream _ =>
      obtain ⟨priorIndex, atPrior⟩ := List.mem_iff_getElem?.mp (List.mem_of_mem_take member)
      obtain ⟨stream, streamDependencies, streamProducer, sameRef, streamKnown⟩ :=
        State.startup_runNormalized_streamReference_refLocated startup valid atPrior
          (List.mem_cons_self : closedStream.ref ∈ streamReferenceRefs _)
      exact generated.groupStreamRefsDisjoint known streamKnown
        (same.trans ((List.mem_singleton.mp closed).trans sameRef.symm))
  | groupValues | streamValues | workQueueTermination => cases closed

/-- Failed-group openness specializes the actual startup closure-lifecycle proof. -/
theorem ExecutedWork.startup_runNormalized_groupFailureOpenAt {work : Execution.Work}
    (startup : InitialStartup) {batches : List (List GraphEvent)}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work batches.flatten)
    (started : inputsStarted work batches startup = true) {index : Nat} {group errors}
    (atEvent
      : ((((State.initialize (Work.fromExecution work) startup)).runNormalized
            batches).2.flatten.flatMap
          publicationAtoms)[index]?
        = some (.groupFailure group errors))
    : let queue := (State.initialize (Work.fromExecution work) startup)
      Open ((queue.initialGroups ++ queue.initialStreams).map Execution.DeliveryNode.ref)
        (((queue.runNormalized batches).2.flatten.flatMap publicationAtoms).take index)
        group.ref :=
  generated.startup_runNormalized_groupClosureOpenAt startup valid started atEvent
    List.mem_cons_self

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
