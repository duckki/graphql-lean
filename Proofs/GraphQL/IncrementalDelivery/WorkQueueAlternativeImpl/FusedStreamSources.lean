import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.FusedDrainSources
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.RegistrationHostEffects
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.RegistrationSnapshotProjection
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.FusedFailureResources

/-! Connect prepared source records to the actual FIFO item handler and its emitted effects.
Generated frames are derived at the real pre-drain boundary. The earlier item cleanup and
post-ACK suffix are tracked together; wire failure notices do not decide disposal.
-/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
open WorkQueueSemantics (Occurrence)
open ReferenceWorkQueue (TaskNode)

private theorem cleanupSource_effect {effects : List HostEffect} {key : Nat}
    (listed : CleanupTarget.stream key ∈ effects.filterMap HostEffect.cleanupStart?)
    : HostEffect.cancelSource key ∈ effects := by
  obtain ⟨effect, emitted, identifies⟩ := List.mem_filterMap.mp listed
  cases effect with
  | cancelSource other =>
      cases CleanupTarget.stream.inj (Option.some.inj identifies)
      exact emitted
  | adopt | acknowledge | abortTask | abortStreamQueue | responseFinished =>
      cases identifies

theorem referencePrefix_inventory (work : Work) (events : List GraphEvent)
    : let queue :=
        (ReferenceWorkQueue.State.initialize
          (ReferenceWorkQueue.Work.fromExecution work)).replayGraphEvents
          events
      queue.ChildStreamInventory := by
  have loop (more : List GraphEvent) (queue : ReferenceWorkQueue.State)
      (inventory : queue.ChildStreamInventory)
      : (queue.replayGraphEvents more).ChildStreamInventory := by
    induction more generalizing queue with
    | nil => exact inventory
    | cons event rest ih => exact ih _ (inventory.handleGraphEvent event)
  exact loop events _ (ReferenceWorkQueue.createWorkQueue_childStreamInventory _)

private theorem prepared_inventory {queue : ReferenceWorkQueue.State}
    (inventory : queue.ChildStreamInventory) (items : List ReferenceWorkQueue.StreamItem)
    : (queue.preparedStreamItems items).ChildStreamInventory :=
  ReferenceWorkQueue.State.preparedStreamItems_preserves
    ReferenceWorkQueue.State.ChildStreamInventory inventory items
    (fun _ item _ prior =>
      ((prior.maybeIntegrateWork item.work).pruneEmptyGroups _).startNewWork _)

-----------------------------------------------------------------------------------------
-- Original generated raw prefixes construct the actual receipt source classification
-----------------------------------------------------------------------------------------

/-- Every prepared held source retains its exact record, becomes active, or gets an actual
cancelSource effect in the same receipt. The source/inventory and owner/forest frames are
constructed, and the target prefix/suffix effect equality is proved independently.
-/
theorem referencePrefix_streamItems_sources {work : Work}
    (generated : ReferenceWorkQueue.ExecutedWork work) (events : List GraphEvent)
    (valid : ReferenceWorkQueue.ValidGraphEvents work events)
    (accepted
      : (ReferenceWorkQueue.State.initialize
          (ReferenceWorkQueue.Work.fromExecution work)).acceptsBatch
          events
        = true)
    (stream : Execution.DeliveryNode) (items : List ReferenceWorkQueue.StreamItem)
    (matched : (ReferenceWorkQueue.GraphEvent.streamItems stream items).MatchesWork work)
    : let queue :=
        (ReferenceWorkQueue.State.initialize
          (ReferenceWorkQueue.Work.fromExecution work)).replayGraphEvents
          events
      ∀ occurrence node key,
        (registrationSnapshot queue (.streamItems stream items)).taskNode? occurrence
          = some node
        → key ∈ node.childStreams
        → let reduced := ({ queue } : State).streamItems stream items
          reduced.1.queue.taskNode? occurrence = some node
          ∨ key ∈ reduced.1.queue.rootStreams
          ∨ .cancelSource key ∈ reduced.2.2 := by
  let queue := (ReferenceWorkQueue.State.initialize
    (ReferenceWorkQueue.Work.fromExecution work)).replayGraphEvents events
  change ∀ occurrence node key,
    (registrationSnapshot queue (.streamItems stream items)).taskNode? occurrence = some node
    → key ∈ node.childStreams
    → let reduced := ({ queue } : State).streamItems stream items
      reduced.1.queue.taskNode? occurrence = some node
      ∨ key ∈ reduced.1.queue.rootStreams
      ∨ .cancelSource key ∈ reduced.2.2
  intro occurrence node key found held
  cases active : queue.rootStreams.contains stream.ref with
  | false =>
      simp only [State.streamItems, active, Bool.not_false, ↓reduceIte,
        registrationSnapshot, Bool.false_eq_true] at found ⊢
      exact .inl found
  | true =>
      let acc := items.foldl streamRegistrationStep (({ queue } : State), [], [], [], [], [])
      rw [registrationSnapshot_itemFold queue stream items active] at found
      have matching := fun event member => valid.eachMatches (event := event) member
      have fold := referencePrefix_streamRegistrationFold generated events matching stream items matched
      have queueEq : acc.1.queue = queue.preparedStreamItems items := congrArg Prod.fst fold
      obtain ⟨parents, frame, forest⟩ := referencePrefix_streamItems_drainFrames
        generated events valid accepted stream items matched
      have actualFrame : acc.1.queue.TaskOwnerFrame work := by rw [queueEq]; exact frame
      have actualForest : acc.1.queue.RemovalForest parents := by rw [queueEq]; exact forest
      have inventory : acc.1.queue.ChildStreamInventory := by
        rw [queueEq]; exact prepared_inventory (referencePrefix_inventory work events) items
      have running : acc.1.stopped = false := streamRegistrationFold_stopped items _
      have unique := (streamRegistrationFold_cleanupTargets items
        (({ queue } : State), [], [], [], [], []) List.nodup_nil rfl).1
      have classified := FusedDrainSourceProgress_holds acc.1 work parents acc.2.2.2.2.1
        running actualFrame actualForest inventory unique occurrence node key found held
      have cleanup := State.streamItems_cleanupStarts_eq ({ queue } : State) stream items active
      simp only [State.streamItems, active, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      rcases classified with retained | released | requested
      · exact .inl retained
      · exact .inr (.inl released)
      · apply Or.inr; apply Or.inr
        have emitted : .cancelSource key ∈ (({ queue } : State).streamItems stream items).2.2 := by
          apply cleanupSource_effect
          rw [cleanup]
          exact requested
        simpa only [State.streamItems, active, Bool.not_true, Bool.false_eq_true,
          ↓reduceIte]
          using emitted

-----------------------------------------------------------------------------------------
-- The generated receipt supplies one compatible resource history
-----------------------------------------------------------------------------------------

/-- Source safety for the actual receipt at generated raw prefixes. Only original generated
work, valid preceding inputs, start acceptance and a matching receipt are supplied. Every
cleanup request is licensed by this same handler's effects; the observer neither acquires
resources nor claims async release. Sources may instead be transferred into active roots.
-/
def GeneratedStreamReceiptResourceSafety : Prop :=
  ∀ (work : Work) (events : List GraphEvent),
    ReferenceWorkQueue.ExecutedWork work
    → ReferenceWorkQueue.ValidGraphEvents work events
    → (ReferenceWorkQueue.State.initialize
        (ReferenceWorkQueue.Work.fromExecution work)).acceptsBatch
        events
      = true
    → ∀ (stream : Execution.DeliveryNode) (items : List ReferenceWorkQueue.StreamItem),
        (ReferenceWorkQueue.GraphEvent.streamItems stream items).MatchesWork work
        → ∀ resources : ResourceState,
            let queue :=
              (ReferenceWorkQueue.State.initialize
                (ReferenceWorkQueue.Work.fromExecution work)).replayGraphEvents
                events
            let reduced := ({ queue } : State).streamItems stream items
            let observed :=
              resources.observeHandlerCleanup { queue } (.streamItems stream items)
            ResourceReplay resources observed.2 observed.1
            ∧ (∀ action ∈ observed.2,
                ∃ effect ∈ reduced.2.2,
                  ∃ target,
                    effect.cleanupStart? = some target ∧ action = .requestCleanup target)
            ∧ ∀ occurrence node key,
                (registrationSnapshot queue (.streamItems stream items)).taskNode?
                    occurrence
                  = some node
                → key ∈ node.childStreams
                → resources (.stream key) = .owned .queue
                → reduced.1.queue.taskNode? occurrence = some node
                  ∨ key ∈ reduced.1.queue.rootStreams
                  ∨ observed.1 (.stream key) = .cleanupRequested .queue

theorem GeneratedStreamReceiptResourceSafety_holds
    : GeneratedStreamReceiptResourceSafety := by
  intro work events generated valid accepted stream items matched resources
  refine ⟨resources.observeHandlerCleanup_replay _ _,
    fun _ member => resources.observeHandlerCleanup_actions _ _ member, ?_⟩
  intro occurrence node key found held owned
  rcases referencePrefix_streamItems_sources generated events valid accepted stream items
      matched occurrence node key found held with retained | active | requested
  · exact .inl retained
  · exact .inr (.inl active)
  · exact .inr (.inr (resources.requestQueueCleanup_owned _ _
      (List.mem_filterMap.mpr ⟨.cancelSource key, requested, rfl⟩) owned))

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
