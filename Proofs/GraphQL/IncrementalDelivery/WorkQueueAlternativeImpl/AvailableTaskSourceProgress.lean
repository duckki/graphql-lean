import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.AvailableSourceDrain
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.FusedTaskSources
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.BufferedStreamRelease

/-! Prepared source records through the actual task-success phases with full availability.
Ready certificates derive from reference cache correspondence, independently of resources.
-/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
open WorkQueueSemantics (Occurrence NodeRefs)
open ReferenceWorkQueue (TaskNode)

/-- Reference settlement and common cache exposure derive all actual ready-source frames. -/
theorem State.taskSuccess_readySourceFrames_available {state : State} {work settled}
    (generated : ReferenceWorkQueue.ExecutedWork work)
    (present : state.queue.RootGroupsPresent)
    (accounted : state.queue.PendingAccounting work settled)
    (keys : state.queue.TaskNodeKeysUnique) (inventory : state.queue.ChildStreamInventory)
    (incoming : Occurrence) (result : ReferenceWorkQueue.TaskResult) (input : TaskNode)
    (found : state.queue.taskNode? incoming = some input) (fresh : incoming ∉ settled)
    (known : ∀ task ∈ result.work.tasks, ReferenceWorkQueue.TaskMatches work task)
    (childFresh : ∀ task ∈ result.work.tasks, task.occurrence ∉ incoming :: settled)
    (running : state.stopped = false) (available : List (Occurrence × Nat))
    (startupFrames
      : ∃ parents,
          (referenceTaskSuccessReleased state.queue incoming result
            input).1.TaskOwnerFrame
            work
          ∧ (referenceTaskSuccessReleased state.queue incoming result
              input).1.RemovalForest
              parents)
    : ∃ parents,
        let active := taskSuccessReadyPhase state incoming result input available
        active.1.queue.TaskOwnerFrame work
        ∧ active.1.queue.RemovalForest parents
        ∧ active.1.queue.TaskNodeKeysUnique
        ∧ active.1.queue.ChildStreamInventory := by
  let active := taskSuccessReadyPhase state incoming result input available
  let released := referenceTaskSuccessReleased state.queue incoming result input
  let reference := released.1.startNewWork released.2.2 available
  have phase := state.taskSuccess_readyCacheProjection generated present accounted keys
    incoming result input found fresh known childFresh running available startupFrames
  have exposed := congrArg Prod.fst phase
  change active.1.queue.cacheTaskFailures available = reference.1.cacheTaskFailures available
    at exposed
  have referenceKeys : reference.1.TaskNodeKeysUnique :=
    (((keys.putTaskNode _).maybeIntegrateWork result.work (some incoming)).successGroupFold
      input.task.groups).startNewWork released.2.2 available
  have actualKeys : active.1.queue.TaskNodeKeysUnique := by
    have cached := referenceKeys.cacheTaskFailures available
    rw [← exposed] at cached
    simpa only [ReferenceWorkQueue.State.TaskNodeKeysUnique,
      ReferenceWorkQueue.State.cacheTaskFailures_taskOccurrences] using cached
  obtain ⟨parents, owners, forest⟩ := startupFrames
  have actualOwners := ReferenceWorkQueue.State.TaskOwnerFrame.of_cacheTaskFailures_eq
    actualKeys available exposed (owners.startNewWork released.2.2 available)
  have actualForest : active.1.queue.RemovalForest parents := by
    have groups := congrArg ReferenceWorkQueue.State.groupNodes exposed
    simp only [ReferenceWorkQueue.State.cacheTaskFailures_groupNodes] at groups
    apply (forest.startNewWork released.2.2 available).of_subset
    rw [groups]
    exact List.Subset.refl _
  have links := inventory input (List.mem_of_find?_eq_some found)
  have referenceInventory : reference.1.ChildStreamInventory :=
    (((inventory.putTaskNode { input with value := some result.value } links.1 links.2
      ).maybeIntegrateWork result.work (some incoming)).successGroupFold input.task.groups [] {}
      ).startNewWork released.2.2 available
  exact ⟨parents, actualOwners, actualForest, actualKeys,
    childStreamInventory_of_cache_eq actualKeys available exposed referenceInventory⟩

/-- A prepared task-success source record reaches an actual endpoint record or source
cleanup. Its rejection slot may change during startup; its value and attachment remain the
resource evidence. The ready frames are independently derived structural certificates.
-/
theorem State.taskSuccess_phaseSourceRecord_available {state : State} {work}
    (incoming : Occurrence) (result : ReferenceWorkQueue.TaskResult) (input : TaskNode)
    (foundInput : state.queue.taskNode? incoming = some input)
    (running : state.stopped = false) (available : List (Occurrence × Nat))
    (keys
      : (registrationSnapshot state.queue
          (.taskSuccess incoming result)).TaskNodeKeysUnique)
    (inventory
      : (registrationSnapshot state.queue
          (.taskSuccess incoming result)).ChildStreamInventory)
    (ready
      : ∃ parents,
          let active := taskSuccessReadyPhase state incoming result input available
          active.1.queue.TaskOwnerFrame work
          ∧ active.1.queue.RemovalForest parents
          ∧ active.1.queue.TaskNodeKeysUnique
          ∧ active.1.queue.ChildStreamInventory)
    {key}
    (represented
      : RecordTargetRepresented
          (registrationSnapshot state.queue (.taskSuccess incoming result)) (.stream key))
    : RecordTargetRepresented (state.taskSuccess incoming result available).1.queue
        (.stream key)
      ∨ .cancelSource key ∈ (state.taskSuccess incoming result available).2.2.1 := by
  let stored : State :=
    { state with queue := state.queue.putTaskNode { input with value := some result.value } }
  let registered := stored.maybeIntegrateWork result.work (some incoming)
  let released := input.task.groups.foldl ReferenceWorkQueue.successGroupStep
    (registered.1.queue, [], {})
  let starting : State := { registered.1 with queue := released.1 }
  let active := taskSuccessReadyPhase state incoming result input available
  have prepared : registrationSnapshot state.queue (.taskSuccess incoming result)
      = registered.1.queue := by
    simp only [registrationSnapshot, foundInput]
    dsimp only [registered, stored]
    rw [running]
  rw [prepared] at keys inventory represented
  have releasedKeys := keys.successGroupFold input.task.groups
  have sourceRelease := registered.1.queue.successGroupFold_streamRelease input.task.groups
  have releasedRecord : RecordTargetRepresented released.1 (.stream key)
      ∨ key ∈ released.2.2.newStreams.map Execution.DeliveryNode.ref := by
    cases represented with
    | activeStream activated =>
        exact .inl (.activeStream (by rw [sourceRelease.1]; exact activated))
    | bufferedStream found stored held =>
        rcases successFold_heldSource input.task.groups (registered.1.queue, [], {})
            inventory found held with kept | transferred
        · exact .inl (.bufferedStream kept stored held)
        · exact .inr transferred
  have startingRunning : starting.stopped = false :=
    (State.maybeIntegrateWork_stopped stored result.work (some incoming)).trans running
  have startup : RecordTargetRepresented active.1.queue (.stream key)
      ∨ .stream key ∈ active.2.2.1 := by
    rcases releasedRecord with kept | transferred
    · exact sourceRecord_startNewWork_available starting releasedKeys released.2.2 registered.2 []
        available kept
    · exact .inl (.activeStream (startup_streamRoots_available starting released.2.2 registered.2 []
        startingRunning sourceRelease.2.2.2 available (List.mem_append_right _ transferred)))
  obtain ⟨parents, frame, forest, readyKeys, readyInventory⟩ := ready
  have activeRunning : active.1.stopped = false :=
    (taskSuccessReadyPhase_stopped state incoming result input available).trans running
  have unique : active.2.2.1.Nodup :=
    State.startNewWork_targets_nodup _ _ _ [] List.nodup_nil available
  rw [state.taskSuccess_eq incoming result input foundInput available]
  have emit (target : .stream key ∈ (active.1.drainReadyGroups active.2.2.1 available).2.2.1)
      : .cancelSource key ∈ [.adopt incoming]
        ++ (active.1.drainReadyGroups active.2.2.1 available).2.2.1.flatMap CleanupTarget.effects :=
    List.mem_append_right _ (List.mem_flatMap.mpr ⟨.stream key, target, List.mem_cons_self⟩)
  rcases startup with kept | requested
  · rcases sourceRecord_drainReadyGroups_available activeRunning frame forest readyInventory
        readyKeys active.2.2.1 unique available kept with retained | cleaned
    · exact .inl retained
    · exact .inr (emit cleaned)
  · exact .inr (emit ((State.drainReadyGroups_targets active.1 active.2.2.1 unique
      available).2.sublist.subset requested))

/-- Source validity and the same actual source-cut frames construct every task-success
phase premise. The resulting resource alternative uses the supplied cache throughout.
-/
theorem sourceFrame_taskSuccess_sourceRecord_available {queue : ReferenceWorkQueue.State}
    {work parents before}
    (generated : ReferenceWorkQueue.ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          ReferenceWorkQueue.GroupRecordAt work node dependencies
          → dependencies = parents node.ref)
    (source : ReferenceWorkQueue.UncancelledReplayFrame queue work parents before)
    (keys : queue.TaskNodeKeysUnique) (initialInventory : queue.ChildStreamInventory)
    (incoming : Occurrence) (result : ReferenceWorkQueue.TaskResult)
    (valid
      : ReferenceWorkQueue.ValidGraphEvents work
          (before ++ [.taskSuccess incoming result]))
    (available : List (Occurrence × Nat)) {key}
    (represented
      : RecordTargetRepresented
          (registrationSnapshot queue (.taskSuccess incoming result)) (.stream key))
    : RecordTargetRepresented
        (({ queue } : State).taskSuccess incoming result available).1.queue (.stream key)
      ∨ .cancelSource key
        ∈ (({ queue } : State).taskSuccess incoming result available).2.2.1 := by
  obtain ⟨prior, matched, freshEvent⟩ := ReferenceWorkQueue.validGraphEvents_last valid
  cases found : queue.taskNode? incoming with
  | none =>
      simp only [registrationSnapshot, found] at represented
      simp only [State.taskSuccess, found]
      exact .inl represented
  | some input =>
      let stored : State :=
        { queue := queue.putTaskNode { input with value := some result.value } }
      have preparedKeys : (registrationSnapshot queue
          (.taskSuccess incoming result)).TaskNodeKeysUnique := by
        simp only [registrationSnapshot, found]
        exact State.maybeIntegrateWork_taskNodeKeysUnique (state := stored) (keys.putTaskNode _)
          result.work (some incoming)
      have originalLinks := initialInventory input (List.mem_of_find?_eq_some found)
      have installed := initialInventory.putTaskNode { input with value := some result.value }
        originalLinks.1 originalLinks.2
      have eager : (eagerRegistrationSnapshot queue
          (.taskSuccess incoming result)).ChildStreamInventory := by
        simp only [eagerRegistrationSnapshot, found]
        exact installed.maybeIntegrateWork result.work (some incoming)
      have projection := snapshotProjection_of_structuralFrames generated canonical
        source.roots.live source.roots.retired source.tasks source.parent.children keys
        (.taskSuccess incoming result) matched
      have preparedInventory : (registrationSnapshot queue
          (.taskSuccess incoming result)).ChildStreamInventory := by
        intro task member
        have captured := eager task (projection.nodes member)
        have streams := congrArg ReferenceWorkQueue.State.streams projection.core
        change (registrationSnapshot queue (.taskSuccess incoming result)).streams
          = (eagerRegistrationSnapshot queue (.taskSuccess incoming result)).streams at streams
        rw [streams]
        exact captured
      have fresh : incoming ∉ ReferenceWorkQueue.GraphEvent.groupSettlements before := by
        intro member
        exact freshEvent.2.2.1 incoming List.mem_cons_self
          (ReferenceWorkQueue.GraphEvent.groupSettlements_subsetIdentities before member)
      have known : ∀ task ∈ result.work.tasks, ReferenceWorkQueue.TaskMatches work task := by
        intro task member
        obtain ⟨address, payload, same, located⟩ := matched.childTask_producer member
        exact ⟨⟨address, payload, some incoming, same, located⟩,
          matched.childTask_groupsExact member⟩
      have childFresh : ∀ task ∈ result.work.tasks,
          task.occurrence ∉ incoming :: ReferenceWorkQueue.GraphEvent.groupSettlements before := by
        intro task member used
        rcases List.mem_cons.mp used with now | earlier
        · exact matched.childTasks_not_success member (List.mem_cons.mpr (.inl now))
        · exact matched.childTasks_unsettled prior freshEvent member
            (ReferenceWorkQueue.GraphEvent.groupSettlements_subsetIdentities before earlier)
      have startup := taskSuccess_startFrames generated source.pending.registration canonical source.roots.live
        source.roots.retired source.tasks source.parent.children incoming result matched input found
      have ready := State.taskSuccess_readySourceFrames_available (state := { queue }) generated
        source.roots.live.present source.pending keys initialInventory incoming result input found
        fresh known childFresh rfl available ⟨parents, startup⟩
      exact State.taskSuccess_phaseSourceRecord_available incoming result input found rfl
        available preparedKeys preparedInventory ready represented

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
