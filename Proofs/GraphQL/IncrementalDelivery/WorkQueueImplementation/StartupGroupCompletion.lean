import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupStreamCompletion
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupCompletionReplay

/-! Historical startup group announcements retain their own actual completion. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

private theorem FifoGroupNoticeCompletion.withInitialMetadata {initial queue events}
    (tracked : FifoGroupNoticeCompletion initial (queue, events))
    (groups streams : List Execution.DeliveryNode)
    : FifoGroupNoticeCompletion initial
        ({ queue with initialGroups := groups, initialStreams := streams }, events) :=
  tracked

/-- Initial group notices retain live or queued support before any host batch is supplied. -/
theorem ExecutedWork.initialStartup_groupNoticeCompletion {work}
    (generated : ExecutedWork work) (startup : InitialStartup)
    : let initial := State.initialize (Work.fromExecution work) startup
      FifoGroupNoticeCompletion
        ((State.initialize (Work.fromExecution work)).initialGroups.map
          Execution.DeliveryNode.ref) (initial, []) := by
  obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
  have parent := initialPreparation_parentCutFrame generated canonical
  have roots : (initialPreparation work).1.RootAncestorsRetired work := by
    intro ref active; rw [initialPreparation_rootGroups_empty] at active; cases active
  have support : ∀ ref ∈ (initialPreparation work).1.rootGroups,
      ∃ dependencies, NodeHasDependencies work ref .group dependencies := by
    intro ref active; rw [initialPreparation_rootGroups_empty] at active; cases active
  have frame : RootClosureFrame (initialPreparation work).1 work parents :=
    ⟨parent.records, parent.links, roots, support⟩
  have frontier := initialPreparation_frontier (work := work)
  have completion := frame.startNewWork_groupNoticeCompletion frontier.1 generated canonical
    (initialPreparation work).2 generated.initialPreparation_retirement.1 frontier.2.2
      startup.failures
  rw [initialPreparation_rootGroups_empty, List.nil_append] at completion
  have pendingEmpty : (initialPreparation work).1.groupFailureEvents = [] := by
    unfold initialPreparation
    rw [State.pruneEmptyGroups_groupFailureEvents, State.maybeIntegrateWork_groupFailureEvents]
  have queued := GroupNoticeCompletion.enqueueGroupFailures (events := [])
    ((initialPreparation work).1.startNewWork (initialPreparation work).2 startup.failures).2
    (by simpa only [List.nil_append, startupControls_eq_failureEvents] using completion)
  simp only [State.pendingGroupFailureRefs, State.startNewWork_groupFailureEvents,
    pendingEmpty, List.map_nil, List.append_nil] at queued
  have tracked := queued.withInitialMetadata (initialPreparation work).2.newGroups
    (initialPreparation work).2.newStreams
  rw [State.initializeWithStartup_eq_preparation]
  exact tracked

/-- Structural replay retains group completion through actual dispatch and queued effects. -/
theorem RootReplayFrame.rawBatches_groupNoticeCompletion {queue work parents}
    (frame : RootReplayFrame queue work parents) (generated : ExecutedWork work)
    (context : queue.RegistrationFrame work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (batches : List (List GraphEvent))
    (matching : ∀ event ∈ batches.flatten, event.MatchesWork work)
    : FifoGroupNoticeCompletion queue.groupNoticeSupport (queue.rawBatches batches) := by
  induction batches generalizing queue with
  | nil => exact .silent (List.Subset.refl _)
  | cons batch rest ih =>
      have matched :=  fun event member => matching event (List.mem_append_left _ member)
      have next := frame.live.handleGraphEvents_groupNoticeCompletion frame.retired generated
        context canonical batch matched
      exact next.2.2.append (ih ⟨next.1, next.2.1⟩
        (context.handleGraphEvents batch matched).1
        (fun event member => matching event (List.mem_append_right _ member)))

/-- Historical initial and carried group notices remain live, queued or actually completed. -/
theorem ExecutedWork.startup_rawBatches_groupNoticeCompletion {work inputs}
    (generated : ExecutedWork work) (startup : InitialStartup)
    (valid : ValidGraphEvents work inputs.flatten)
    : let initial := State.initialize (Work.fromExecution work) startup
      FifoGroupNoticeCompletion
        ((State.initialize (Work.fromExecution work)).initialGroups.map
          Execution.DeliveryNode.ref)
        (initial.rawBatches inputs) := by
  obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
  have context := (generated.initialStartup_parentCutFrame canonical startup).registration
  have replay := (generated.initialStartup_rootReplayFrame canonical
    startup).rawBatches_groupNoticeCompletion generated context canonical inputs
      (fun event member => valid.event_matches member)
  exact (generated.initialStartup_groupNoticeCompletion startup).append replay

namespace ConformancePlan

/-- Exact actual startup group notices and completions survive publisher atomization. -/
theorem startup_groupNoticeRefs_tracked {work inputs} {w : Witness}
    (generated : ExecutedWork work) (startup : InitialStartup)
    (valid : ValidGraphEvents work inputs.flatten)
    (ended
      : let initial := State.initialize (Work.fromExecution work) startup
        (initial.runNormalized inputs).1.terminated = true)
    (history
      : let initial := State.initialize (Work.fromExecution work) startup
        w.events = initial.nonterminalAtoms inputs)
    : ∀ ref ∈
        (initialQueue work).initialGroups.map Execution.DeliveryNode.ref
        ++ w.events.flatMap groupNoticeRefs,
        ref
          ∈ ((State.initialize (Work.fromExecution work) startup).runNormalized
              inputs).1.rootGroups
        ∨ ref ∈ w.events.flatMap groupClosureRefs := by
  let initial := State.initialize (Work.fromExecution work) startup
  let publisher : IncrementalPublisher :=
    { active := initial.initialGroups ++ initial.initialStreams }
  have noticeProjection := atomicGroupNotices publisher
    (initial.rawBatches inputs).2
    (initial.rawBatches_nonemptyValues inputs valid.nonemptyItems)
  rw [Witness.startup_rawBatches_shape startup history] at noticeProjection
  have notices : w.events.flatMap groupNoticeRefs
      = (initial.rawBatches inputs).2.flatMap rawGroupNoticeRefs := by
    split at noticeProjection
    <;> simpa [List.flatMap_append, groupNoticeRefs] using noticeProjection
  have closureProjection : ((publisher.normalizeBatch
      (initial.rawBatches inputs).2).2.flatMap publicationAtoms).flatMap
      groupClosureRefs = (initial.rawBatches inputs).2.flatMap
        rawGroupClosureRefs := by
    rw [List.flatMap_assoc]
    simp only [publicationAtoms_groupClosureRefs,
      IncrementalPublisher.normalizeBatch_groupClosureRefs]
  rw [Witness.startup_rawBatches_shape startup history] at closureProjection
  have closures : w.events.flatMap groupClosureRefs
      = (initial.rawBatches inputs).2.flatMap rawGroupClosureRefs := by
    split at closureProjection
    <;> simpa [List.flatMap_append, groupClosureRefs] using closureProjection
  intro ref member
  rw [notices] at member
  have empty := initial.runNormalized_terminalPending (by
    rw [State.initializeWithStartup_terminated]
    intro impossible; cases impossible) inputs ended
  rw [State.runNormalized_replayBatches, ← State.rawBatches_state] at empty
  have tracked := (generated.startup_rawBatches_groupNoticeCompletion startup valid).completed
    empty ref member
  rw [State.rawBatches_state, ← State.runNormalized_replayBatches] at tracked
  rwa [← closures] at tracked

end ConformancePlan
end GraphQL.IncrementalDelivery.ReferenceWorkQueue
