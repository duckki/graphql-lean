import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.FusedStreamSources
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.PublicationReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.UncancelledReplay

/-! Source transfer through the actual accepted task-success owner fold, delayed activation
and fused ready drain. Exact phase projection reuses the existing settlement proof.
-/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
open WorkQueueSemantics (NodeRefs Occurrence)
open ReferenceWorkQueue (TaskNode)

-----------------------------------------------------------------------------------------
-- Shared successful settlement either retains a record or releases its held sources
-----------------------------------------------------------------------------------------

private theorem successFold_released (groups : List Execution.DeliveryNode)
    (acc
      : ReferenceWorkQueue.State
        × List Execution.WorkQueueEvent
        × ReferenceWorkQueue.NewWork)
    {key : Nat} (released : key ∈ acc.2.2.newStreams.map Execution.DeliveryNode.ref)
    : key
      ∈ (groups.foldl ReferenceWorkQueue.successGroupStep acc).2.2.newStreams.map
          Execution.DeliveryNode.ref := by
  induction groups generalizing acc with
  | nil => exact released
  | cons group rest ih =>
      rw [List.foldl_cons]
      apply ih
      unfold ReferenceWorkQueue.successGroupStep
      dsimp only
      split
      · exact released
      · split
        · simp only [List.map_append]
          exact List.mem_append_left _ released
        · exact released

private theorem successFold_inventory (groups : List Execution.DeliveryNode)
    (acc
      : ReferenceWorkQueue.State
        × List Execution.WorkQueueEvent
        × ReferenceWorkQueue.NewWork)
    (inventory : acc.1.ChildStreamInventory)
    : (groups.foldl ReferenceWorkQueue.successGroupStep acc).1.ChildStreamInventory := by
  induction groups generalizing acc with
  | nil => exact inventory
  | cons group rest ih =>
      rw [List.foldl_cons]
      apply ih
      unfold ReferenceWorkQueue.successGroupStep
      dsimp only
      split
      · exact inventory
      · split
        · exact (inventory.putGroupNode _).finishGroupSuccess _
        · exact inventory.putGroupNode _

/-- The literal shared owner fold transfers selected held sources into its real release
list; unselected sources keep their exact producer record. Its catalogue inventory, not
an output-filter predicate, justifies each source descriptor.
-/
theorem successFold_heldSource (groups : List Execution.DeliveryNode)
    (acc
      : ReferenceWorkQueue.State
        × List Execution.WorkQueueEvent
        × ReferenceWorkQueue.NewWork)
    (inventory : acc.1.ChildStreamInventory) {occurrence node key}
    (found : acc.1.taskNode? occurrence = some node) (held : key ∈ node.childStreams)
    : let next := groups.foldl ReferenceWorkQueue.successGroupStep acc
      next.1.taskNode? occurrence = some node
      ∨ key ∈ next.2.2.newStreams.map Execution.DeliveryNode.ref := by
  induction groups generalizing acc with
  | nil => exact .inl found
  | cons group rest ih =>
      rw [List.foldl_cons]
      unfold ReferenceWorkQueue.successGroupStep
      dsimp only
      split
      · exact ih _ inventory found
      · rename_i owner lookup
        let updated := { owner with pending := owner.pending - 1 }
        let current := acc.1.putGroupNode updated
        have prior : current.ChildStreamInventory := inventory.putGroupNode updated
        have lookup : current.taskNode? occurrence = some node := found
        split
        · by_cases listed : occurrence ∈ owner.tasks
          · apply Or.inr
            apply successFold_released
            rw [List.map_append]
            apply List.mem_append_right
            exact prior.finishGroupSuccess_childRef_covered updated listed lookup held
          · exact ih _ (prior.finishGroupSuccess updated)
              ((current.finishGroupSuccess_lookup_unselected updated listed).trans lookup)
        · exact ih _ prior lookup

-----------------------------------------------------------------------------------------
-- Compose the actual pre-drain phase and cumulative cleanup, on one endpoint
-----------------------------------------------------------------------------------------

/-- Local accepted-handler source classification. The actual prepared inventory and ready
frames are phase invariants; generated constructions below supply them independently.
-/
theorem taskSuccess_phaseSource {state : State} {work : Work} {parents : Nat → NodeRefs}
    (incoming : Occurrence) (result : ReferenceWorkQueue.TaskResult) (input : TaskNode)
    (running : state.stopped = false)
    (inventory
      : (registrationSnapshot state.queue
          (.taskSuccess incoming result)).ChildStreamInventory)
    (foundInput : state.queue.taskNode? incoming = some input)
    (frame
      : (taskSuccessReadyPhase state incoming result input).1.queue.TaskOwnerFrame work)
    (forest
      : (taskSuccessReadyPhase state incoming result input).1.queue.RemovalForest parents)
    (readyInventory
      : (taskSuccessReadyPhase state incoming result input).1.queue.ChildStreamInventory)
    {occurrence node key}
    (found
      : (registrationSnapshot state.queue (.taskSuccess incoming result)).taskNode?
          occurrence
        = some node) (held : key ∈ node.childStreams)
    : (state.taskSuccess incoming result).1.queue.taskNode? occurrence = some node
      ∨ key ∈ (state.taskSuccess incoming result).1.queue.rootStreams
      ∨ .cancelSource key ∈ (state.taskSuccess incoming result).2.2.1 := by
  let stored : State := { state with
    queue := state.queue.putTaskNode { input with value := some result.value } }
  let registered := stored.maybeIntegrateWork result.work (some incoming)
  let released := input.task.groups.foldl ReferenceWorkQueue.successGroupStep
    (registered.1.queue, [], {})
  let active := taskSuccessReadyPhase state incoming result input
  have prepared : registrationSnapshot state.queue (.taskSuccess incoming result)
      = registered.1.queue := by
    simp only [registrationSnapshot, foundInput]
    cases state with
    | mk queue stopped =>
        cases stopped with
        | false => rfl
        | true => cases running
  rw [prepared] at inventory found
  have classified := successFold_heldSource input.task.groups (registered.1.queue, [], {})
    inventory found held
  have activeRunning : active.1.stopped = false :=
    (taskSuccessReadyPhase_stopped state incoming result input).trans running
  have unique : active.2.2.1.Nodup := State.startNewWork_targets_nodup _ _ _ [] List.nodup_nil
  rw [state.taskSuccess_eq incoming result input foundInput]
  change (active.1.drainReadyGroups active.2.2.1).1.queue.taskNode? occurrence = some node
    ∨ key ∈ (active.1.drainReadyGroups active.2.2.1).1.queue.rootStreams
    ∨ .cancelSource key ∈ ([.adopt incoming] ++
      (active.1.drainReadyGroups active.2.2.1).2.2.1.flatMap CleanupTarget.effects)
  have requested_stays (requested : CleanupTarget.stream key ∈ active.2.2.1)
      : .cancelSource key ∈ [.adopt incoming] ++
          (active.1.drainReadyGroups active.2.2.1).2.2.1.flatMap CleanupTarget.effects := by
    obtain ⟨suffix, same⟩ :=
      (active.1.drainReadyGroups_go_targets active.1.queue.groupNodes.length
        active.2.2.1 unique).2
    have listed : CleanupTarget.stream key ∈ (active.1.drainReadyGroups active.2.2.1).2.2.1 := by
      change CleanupTarget.stream key ∈ (State.drainReadyGroups.go []
        active.1.queue.groupNodes.length active.1 active.2.2.1).2.2.1
      rw [← same]
      exact List.mem_append_left _ requested
    exact List.mem_append_right _ (List.mem_flatMap.mpr
      ⟨.stream key, listed, List.mem_cons_self⟩)
  rcases classified with retained | transferred
  · have startup := startup_heldSource { registered.1 with queue := released.1 }
      released.2.2 registered.2 [] retained held
    rcases startup with kept | requested
    · rcases FusedDrainSourceProgress_holds active.1 work parents active.2.2.1 activeRunning
          frame forest
          readyInventory unique occurrence node key kept held with final | started | requested
      · exact .inl final
      · exact .inr (.inl started)
      · exact .inr (.inr (List.mem_append_right _
          (List.mem_flatMap.mpr ⟨.stream key, requested, List.mem_cons_self⟩)))
    · exact .inr (.inr (requested_stays requested))
  · have started : key ∈ active.1.queue.rootStreams := by
      exact startup_streamRoots { registered.1 with queue := released.1 }
        released.2.2 registered.2 []
        ((stored.maybeIntegrateWork_stopped result.work (some incoming)).trans running)
        (registered.1.queue.successGroupFold_streamRelease input.task.groups).2.2.2
        (List.mem_append_right _ transferred)
    apply Or.inr; apply Or.inl
    rw [congrArg (fun reduction => reduction.1.rootStreams)
      (active.1.drainReadyGroups_projection activeRunning frame forest active.2.2.1)]
    exact ReferenceWorkQueue.State.drainReadyGroups_go_streamRoots_cover _ active.1.queue []
      (List.mem_append_left _ started)

-----------------------------------------------------------------------------------------
-- Generated source prefixes construct every local phase premise
-----------------------------------------------------------------------------------------

private theorem buffered_ne_input {work events incoming result occurrence node}
    (valid
      : ReferenceWorkQueue.ValidGraphEvents work
          (events ++ [.taskSuccess incoming result]))
    (found
      : (ReferenceWorkQueue.State.replayGraphEvents
          (ReferenceWorkQueue.State.initialize
            (ReferenceWorkQueue.Work.fromExecution work))
          events).taskNode?
          occurrence
        = some node)
    (stored : node.value.isSome = true)
    : occurrence ≠ incoming := by
  obtain ⟨prior, _, fresh⟩ := ReferenceWorkQueue.validGraphEvents_last valid
  cases value : node.value with
  | none => simp [value] at stored
  | some payload =>
      obtain ⟨published, _, inventory⟩ :=
        ReferenceWorkQueue.createWorkQueue_rawEventReplay_publications prior
      rw [ReferenceWorkQueue.State.rawEventReplay_state] at inventory
      have known := ReferenceWorkQueue.State.taskNode?_some found
      have provenance := (inventory.stored node known.1 payload value).1
      rw [known.2] at provenance
      intro same
      exact fresh.2.2.1 incoming List.mem_cons_self (same ▸ provenance.identity)

/-- Generated task-success source classification on actual accepted prefixes, including
ignored unhealthy inputs. An older stored buffer cannot be the fresh settling input.
Ready frames reuse the existing settlement projection; source inventory is independently
derived before registration and throughout the shared owner/start calculation.
-/
theorem referencePrefix_taskSuccess_sources {work : Work}
    (generated : ReferenceWorkQueue.ExecutedWork work) (events : List GraphEvent)
    (incoming : Occurrence) (result : ReferenceWorkQueue.TaskResult)
    (valid
      : ReferenceWorkQueue.ValidGraphEvents work
          (events ++ [.taskSuccess incoming result]))
    (accepted
      : ReferenceWorkQueue.State.eventsStarted []
          (ReferenceWorkQueue.State.initialize
            (ReferenceWorkQueue.Work.fromExecution work)) events
        = true)
    : let queue :=
        (ReferenceWorkQueue.State.initialize
          (ReferenceWorkQueue.Work.fromExecution work)).replayGraphEvents
          events
      ∀ occurrence node key,
        (registrationSnapshot queue (.taskSuccess incoming result)).taskNode? occurrence
          = some node
        → node.value.isSome = true
        → key ∈ node.childStreams
        → let reduced := ({ queue } : State).taskSuccess incoming result
          reduced.1.queue.taskNode? occurrence = some node
          ∨ key ∈ reduced.1.queue.rootStreams
          ∨ .cancelSource key ∈ reduced.2.2.1 := by
  let queue := (ReferenceWorkQueue.State.initialize
    (ReferenceWorkQueue.Work.fromExecution work)).replayGraphEvents events
  change ∀ occurrence node key,
    (registrationSnapshot queue (.taskSuccess incoming result)).taskNode? occurrence = some node
    → node.value.isSome = true
    → key ∈ node.childStreams
    → let reduced := ({ queue } : State).taskSuccess incoming result
      reduced.1.queue.taskNode? occurrence = some node
      ∨ key ∈ reduced.1.queue.rootStreams
      ∨ .cancelSource key ∈ reduced.2.2.1
  intro occurrence node key found stored held
  cases selected : queue.taskNode? incoming with
  | none =>
      simp only [registrationSnapshot, selected] at found
      simp only [State.taskSuccess, selected]
      exact .inl found
  | some input =>
      have initial := referencePrefix_inventory work events
      have links := initial input (ReferenceWorkQueue.State.taskNode?_some selected).1
      have installed := initial.putTaskNode { input with value := some result.value }
        links.1 links.2
      have eager : (eagerRegistrationSnapshot queue
          (.taskSuccess incoming result)).ChildStreamInventory := by
        simp only [eagerRegistrationSnapshot, selected]
        exact installed.maybeIntegrateWork result.work (some incoming)
      have projection := referencePrefix_snapshotProjection generated events
        (.taskSuccess incoming result) valid
      have inventory : (registrationSnapshot queue
          (.taskSuccess incoming result)).ChildStreamInventory := by
        intro task member
        have prior := eager task (projection.nodes member)
        have registry := congrArg ReferenceWorkQueue.State.streams projection.core
        change (registrationSnapshot queue (.taskSuccess incoming result)).streams
          = (eagerRegistrationSnapshot queue (.taskSuccess incoming result)).streams at registry
        rw [registry]
        exact prior
      let active := taskSuccessReadyPhase ({ queue } : State) incoming result input
      have phase : active.1.queue = referenceTaskSuccessReady queue incoming result input :=
        referencePrefix_taskSuccess_readyProjection generated events incoming result valid
          accepted input selected
      obtain ⟨parents, frame, forest⟩ := referencePrefix_taskSuccess_drainFrames
        generated events incoming result valid accepted input selected
      have actualFrame : active.1.queue.TaskOwnerFrame work := by rw [phase]; exact frame
      have actualForest : active.1.queue.RemovalForest parents := by rw [phase]; exact forest
      have readyInventory : active.1.queue.ChildStreamInventory := by
        rw [phase]
        unfold referenceTaskSuccessReady
        let prepared := ((queue.putTaskNode
          { input with value := some result.value }).maybeIntegrateWork
          result.work (some incoming)).1
        let released := input.task.groups.foldl ReferenceWorkQueue.successGroupStep
          (prepared, [], {})
        exact (successFold_inventory input.task.groups (prepared, [], {})
          (installed.maybeIntegrateWork result.work (some incoming))).startNewWork released.2.2
      exact taskSuccess_phaseSource incoming result input rfl inventory selected
        actualFrame actualForest readyInventory found held

/-- A task-success source classification uses the actual source-accounting state.
Witness: the source frame and structural startup certificates construct the exact ready
phase. No acceptance or state equality with a flattened earlier history is required.
-/
theorem sourceFrame_taskSuccess_sources {queue : ReferenceWorkQueue.State}
    {work : Work} {parents : Nat → WorkQueueSemantics.NodeRefs} {before : List GraphEvent}
    (generated : ReferenceWorkQueue.ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          ReferenceWorkQueue.GroupRecordAt work node dependencies
          → dependencies = parents node.ref)
    (sourceFrame : ReferenceWorkQueue.UncancelledReplayFrame queue work parents before)
    (keys : queue.TaskNodeKeysUnique) (initial : queue.ChildStreamInventory)
    (incoming : Occurrence) (result : ReferenceWorkQueue.TaskResult)
    (valid
      : ReferenceWorkQueue.ValidGraphEvents work
          (before ++ [.taskSuccess incoming result]))
    {occurrence node key}
    (found
      : (registrationSnapshot queue (.taskSuccess incoming result)).taskNode? occurrence
        = some node) (held : key ∈ node.childStreams)
    : (({ queue } : State).taskSuccess incoming result).1.queue.taskNode? occurrence
        = some node
      ∨ key ∈ (({ queue } : State).taskSuccess incoming result).1.queue.rootStreams
      ∨ .cancelSource key ∈ (({ queue } : State).taskSuccess incoming result).2.2.1 := by
  obtain ⟨priorValid, matched, freshEvent⟩ := ReferenceWorkQueue.validGraphEvents_last valid
  cases selected : queue.taskNode? incoming with
  | none =>
      simp only [registrationSnapshot, selected] at found
      simp only [State.taskSuccess, selected]
      exact .inl found
  | some input =>
      have links := initial input (ReferenceWorkQueue.State.taskNode?_some selected).1
      have installed := initial.putTaskNode { input with value := some result.value }
        links.1 links.2
      have eager : (eagerRegistrationSnapshot queue
          (.taskSuccess incoming result)).ChildStreamInventory := by
        simp only [eagerRegistrationSnapshot, selected]
        exact installed.maybeIntegrateWork result.work (some incoming)
      have projection := snapshotProjection_of_structuralFrames generated canonical
        sourceFrame.roots.live sourceFrame.roots.retired sourceFrame.tasks
        sourceFrame.parent.children keys (.taskSuccess incoming result) matched
      have inventory : (registrationSnapshot queue
          (.taskSuccess incoming result)).ChildStreamInventory := by
        intro task member
        have prior := eager task (projection.nodes member)
        have registry := congrArg ReferenceWorkQueue.State.streams projection.core
        change (registrationSnapshot queue (.taskSuccess incoming result)).streams
          = (eagerRegistrationSnapshot queue (.taskSuccess incoming result)).streams at registry
        rw [registry]
        exact prior
      have startup := taskSuccess_startFrames generated sourceFrame.pending.registration canonical sourceFrame.roots.live
        sourceFrame.roots.retired sourceFrame.tasks sourceFrame.parent.children incoming result
        matched input selected
      have fresh : incoming ∉ ReferenceWorkQueue.GraphEvent.groupSettlements before :=
        fun settled => freshEvent.2.2.1 incoming List.mem_cons_self
          (ReferenceWorkQueue.GraphEvent.groupSettlements_subsetIdentities before settled)
      have known : ∀ task ∈ result.work.tasks, ReferenceWorkQueue.TaskMatches work task := by
        intro task member
        obtain ⟨address, payload, same, known⟩ := matched.childTask_producer member
        exact ⟨⟨address, payload, some incoming, same, known⟩,
          matched.childTask_groupsExact member⟩
      have childFresh : ∀ task ∈ result.work.tasks,
          task.occurrence ∉ incoming :: ReferenceWorkQueue.GraphEvent.groupSettlements before := by
        intro task member settled
        rcases List.mem_cons.mp settled with current | earlier
        · exact matched.childTasks_not_success member (List.mem_cons.mpr (.inl current))
        · exact matched.childTasks_unsettled priorValid freshEvent member
            (ReferenceWorkQueue.GraphEvent.groupSettlements_subsetIdentities before earlier)
      have phase := congrArg Prod.fst (State.taskSuccess_readyProjection (state := { queue })
        generated sourceFrame.roots.live.present sourceFrame.pending incoming result input selected
        fresh known childFresh rfl ⟨parents, startup⟩)
      change (taskSuccessReadyPhase { queue } incoming result input).1.queue
        = referenceTaskSuccessReady queue incoming result input at phase
      let released := referenceTaskSuccessReleased queue incoming result input
      have readyFrame :
          (referenceTaskSuccessReady queue incoming result input).TaskOwnerFrame work :=
        startup.1.startNewWork released.2.2 []
      have readyForest :
          (referenceTaskSuccessReady queue incoming result input).RemovalForest parents :=
        startup.2.startNewWork released.2.2 []
      have readyInventory :
          (referenceTaskSuccessReady queue incoming result input).ChildStreamInventory := by
        unfold referenceTaskSuccessReady
        let prepared := ((queue.putTaskNode
          { input with value := some result.value }).maybeIntegrateWork
            result.work (some incoming)).1
        exact (successFold_inventory input.task.groups (prepared, [], {})
          (installed.maybeIntegrateWork result.work (some incoming))).startNewWork released.2.2
      exact taskSuccess_phaseSource incoming result input rfl inventory selected
        (by rw [phase]; exact readyFrame)
        (by rw [phase]; exact readyForest)
        (by rw [phase]; exact readyInventory)
        found held

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
