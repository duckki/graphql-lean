import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupItemStreamFreshness
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamAnnouncementReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.CanonicalStreamCompletion

/-! Actual startup stream announcements form one globally unique inventory. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

private theorem State.StreamAnnouncementInventory.withInitialMetadata {queue : State}
    {announced : NodeRefs} (inventory : queue.StreamAnnouncementInventory announced)
    (notices : List GroupFailureEvent) (groups streams : List Execution.DeliveryNode)
    : ({
            queue with
              groupFailureEvents := notices
              initialGroups := groups
              initialStreams := streams
          }
        : State).StreamAnnouncementInventory
        announced :=
  ⟨inventory.unique, inventory.registered, inventory.stored, inventory.unreleased⟩

/-- Synchronous failed group activation preserves the initial stream announcement inventory. -/
theorem State.initializeWithStartup_streamAnnouncementInventory (work : Execution.Work)
    (startup : InitialStartup)
    : (State.initialize (Work.fromExecution work) startup).StreamAnnouncementInventory
        ((State.initialize (Work.fromExecution work)).initialStreams.map
          Execution.DeliveryNode.ref) := by
  have empty : ({} : State).StreamAnnouncementInventory [] := by
    refine ⟨by simp, ?_, ?_, ?_⟩
    · intro ref impossible; cases impossible
    · intro node impossible; cases impossible
    · intro node impossible; cases impossible
  let integrated := ({} : State).maybeIntegrateWork (Work.fromExecution work)
  let pruned := integrated.1.pruneEmptyGroups integrated.2.newGroups
  have ready := ((empty.maybeIntegrateWork (Work.fromExecution work)).pruneEmptyGroups
    integrated.2.newGroups).startNewWork { integrated.2 with newGroups := pruned.2 }
      startup.failures
  rw [State.initializeWithStartup_eq_preparation]
  exact ready.withInitialMetadata _ _ _

/-- The same stream inventory follows real host-batch state transitions.
Its raw notice projection ignores only the initial failure forwarding controls.
-/
theorem State.StreamAnnouncementInventory.rawBatches {queue work announced}
    (inventory : State.StreamAnnouncementInventory queue announced)
    (matching : queue.ChildStreamsMatchWork work) (generated : ExecutedWork work)
    (batches : List (List GraphEvent))
    (sources : ∀ event ∈ batches.flatten, event.MatchesWork work)
    : (queue.rawBatches batches).1.StreamAnnouncementInventory
        (announced ++ (queue.rawBatches batches).2.flatMap rawStreamNoticeRefs) := by
  induction batches generalizing queue announced with
  | nil =>
      simpa only [State.rawBatches, List.flatMap_nil, List.append_nil] using inventory
  | cons batch rest ih =>
      have first : ∀ event ∈ batch, event.MatchesWork work :=
        fun event member => sources event (List.mem_append_left _ member)
      have next := inventory.handleGraphEvents matching generated batch first
      have last := ih next (matching.handleGraphEvents batch first)
        (fun event member => sources event (List.mem_append_right _ member))
      simpa only [State.rawBatches, List.flatMap_append, List.append_assoc] using last

/-- Initial and actual startup raw stream notices are globally distinct.
The proof uses source-handler state, retaining the actual seeded output's notice projection.
-/
theorem ExecutedWork.startup_rawBatches_streamNoticeRefs_nodup {work inputs}
    (generated : ExecutedWork work) (startup : InitialStartup)
    (valid : ValidGraphEvents work inputs.flatten)
    : let initial := State.initialize (Work.fromExecution work) startup
      ((State.initialize (Work.fromExecution work)).initialStreams.map
          Execution.DeliveryNode.ref
        ++ (initial.rawBatches inputs).2.flatMap rawStreamNoticeRefs).Nodup := by
  let initial := State.initialize (Work.fromExecution work) startup
  have registry := (State.initializeWithStartup_streamAnnouncementInventory work startup).rawBatches
    (State.initializeWithStartup_childStreamsMatchWork _ startup work) generated inputs
    (fun event member => valid.event_matches member)
  exact registry.unique

namespace ConformancePlan

/-- Atomic splitting and the actual publisher preserve the entire stream-notice inventory. -/
theorem startup_streamNoticeRefs_nodup {work inputs} {w : Witness}
    (generated : ExecutedWork work) (startup : InitialStartup)
    (valid : ValidGraphEvents work inputs.flatten)
    (_started : inputsStarted work inputs startup = true)
    (history
      : w.events
        = ((State.initialize (Work.fromExecution work) startup)).nonterminalAtoms inputs)
    : ((initialQueue work).initialStreams.map Execution.DeliveryNode.ref
        ++ w.events.flatMap streamNoticeRefs).Nodup := by
  let initial := State.initialize (Work.fromExecution work) startup
  let publisher : IncrementalPublisher :=
    { active := initial.initialGroups ++ initial.initialStreams }
  have controls := atomicStreamNotices publisher
    (initial.rawBatches inputs).2
    (initial.rawBatches_nonemptyValues inputs valid.nonemptyItems)
  rw [Witness.startup_rawBatches_shape startup history] at controls
  have same : w.events.flatMap streamNoticeRefs
      = (initial.rawBatches inputs).2.flatMap rawStreamNoticeRefs := by
    split at controls <;> simpa [List.flatMap_append, streamNoticeRefs] using controls
  rw [same]
  exact generated.startup_rawBatches_streamNoticeRefs_nodup startup valid

end ConformancePlan
end GraphQL.IncrementalDelivery.ReferenceWorkQueue
