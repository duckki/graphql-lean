import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupStreamInventory
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupContributorRootReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.CanonicalStreamCompletion

/-! Actual startup stream notices retain roots until their observed stream completions. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Every initial startup stream notice is actually activated, including empty streams. -/
theorem State.initializeWithStartup_initialStreams_active (work : Work)
    (startup : InitialStartup)
    : ((State.initialize work startup).initialStreams.map
        Execution.DeliveryNode.ref).Subset
        (State.initialize work startup).rootStreams := by
  unfold State.initialize
  let integrated := ({} : State).maybeIntegrateWork work
  let pruned := integrated.1.pruneEmptyGroups integrated.2.newGroups
  have registered : integrated.2.newStreams.Subset (pruned.1.streams.map Stream.node) := by
    rw [State.pruneEmptyGroups_streams]
    exact (({} : State).maybeIntegrateWork_streams_registered work).2
  have covered := pruned.1.startNewWork_streamRoots_cover
    { integrated.2 with newGroups := pruned.2 } registered startup.failures
  intro ref member
  exact covered (List.mem_append_right _ member)

namespace ConformancePlan

/-- The actual startup nonterminal history retains exact raw stream-notice refs. -/
theorem Witness.startup_streamNotices_eq_raw {work inputs} {w : Witness}
    (startup : InitialStartup) (valid : ValidGraphEvents work inputs.flatten)
    (history
      : let initial := State.initialize (Work.fromExecution work) startup
        w.events = initial.nonterminalAtoms inputs)
    : let initial := State.initialize (Work.fromExecution work) startup
      w.events.flatMap streamNoticeRefs
      = (initial.rawBatches inputs).2.flatMap rawStreamNoticeRefs := by
  let initial := State.initialize (Work.fromExecution work) startup
  let publisher : IncrementalPublisher :=
    { active := initial.initialGroups ++ initial.initialStreams }
  have controls := atomicStreamNotices publisher
    (initial.rawBatches inputs).2
    (initial.rawBatches_nonemptyValues inputs valid.nonemptyItems)
  rw [Witness.startup_rawBatches_shape startup history] at controls
  split at controls <;> simpa [List.flatMap_append, streamNoticeRefs] using controls

/-- Every stream announced in terminal startup replay has an actual observed completion.
Initial diagnostics affect neither stream-root state nor stream notice/closure projections.
-/
theorem startup_streamNoticeRefs_terminalCompleted {work inputs ref} {w : Witness}
    (startup : InitialStartup) (valid : ValidGraphEvents work inputs.flatten)
    (history
      : let initial := State.initialize (Work.fromExecution work) startup
        w.events = initial.nonterminalAtoms inputs)
    (ended
      : let initial := State.initialize (Work.fromExecution work) startup
        (initial.runNormalized inputs).1.terminated = true)
    (noticed
      : ref
        ∈ (initialQueue work).initialStreams.map Execution.DeliveryNode.ref
          ++ w.events.flatMap streamNoticeRefs)
    : ref ∈ completedRefs w.events := by
  let initial := State.initialize (Work.fromExecution work) startup
  let publisher : IncrementalPublisher :=
    { active := initial.initialGroups ++ initial.initialStreams }
  have noticeProjection := Witness.startup_streamNotices_eq_raw startup valid history
  have closureProjection : ((publisher.normalizeBatch
      (initial.rawBatches inputs).2).2.flatMap publicationAtoms).flatMap
      streamClosureRefs = (initial.rawBatches inputs).2.flatMap
        rawStreamClosureRefs := by
    rw [List.flatMap_assoc]
    simp only [publicationAtoms_streamClosureRefs,
      IncrementalPublisher.normalizeBatch_streamClosureRefs]
  rw [Witness.startup_rawBatches_shape startup history] at closureProjection
  have closures : w.events.flatMap streamClosureRefs
      = (initial.rawBatches inputs).2.flatMap rawStreamClosureRefs := by
    have same : w.events.flatMap streamClosureRefs
        = (initial.rawBatches inputs).2.flatMap rawStreamClosureRefs := by
      split at closureProjection
      <;> simpa [List.flatMap_append, streamClosureRefs] using closureProjection
    exact same
  rw [noticeProjection] at noticed
  have actualNotice : ref ∈ initial.rootStreams
      ++ (initial.rawBatches inputs).2.flatMap rawStreamNoticeRefs := by
    rcases List.mem_append.mp noticed with root | later
    · apply List.mem_append_left
      apply State.initializeWithStartup_initialStreams_active
      rwa [State.initializeWithStartup_initialStreams]
    · exact List.mem_append_right _ later
  have tracked := initial.rawBatches_streamNoticeCompletion inputs ref actualNotice
  have empty := initial.runNormalized_terminalRoots (by
    rw [State.initializeWithStartup_terminated]
    intro impossible; cases impossible) inputs ended
  have roots : (initial.rawBatches inputs).1.rootStreams = [] := by
    rw [State.rawBatches_state]
    rw [State.runNormalized_replayBatches] at empty
    exact empty.2
  have completed := tracked.resolve_left (by rw [roots]; simp)
  apply streamClosureRefs_subset_completed
  rwa [closures]

end ConformancePlan
end GraphQL.IncrementalDelivery.ReferenceWorkQueue
