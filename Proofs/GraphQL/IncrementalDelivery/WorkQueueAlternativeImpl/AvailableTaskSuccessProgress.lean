import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.FusedUnsettledTaskDrain
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.RegistrationTaskRetention
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.UnsettledTaskRelease
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupNoticeTaskProvenance

/-! Task-success resource progress at a local source cut with a supplied failure snapshot.
Phase certificates concern structural registration and ownership, not resource endpoints.
-/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
open WorkQueueSemantics (Occurrence NodeRefs)
open GraphQL.IncrementalDelivery.Execution (DeliveryNode)

private theorem ownerLookup {queue : ReferenceWorkQueue.State} {key}
    (present : key ∈ queue.groupNodes.map (fun node => node.group.node.ref))
    : ∃ node, queue.groupNode? key = some node := by
  cases found : queue.groupNode? key with
  | some node => exact ⟨node, rfl⟩
  | none => exact False.elim ((queue.groupNode?_eq_none_iff key).mp found present)

/-- An unfinished task survives the actual success handler or receives its inline abort.
Startup and draining retain supplied availability; only the tracked task is excluded from
that snapshot. All other cached task rejections, including later notifications, are allowed.
-/
theorem State.taskSuccess_preparedTask_progress_available {state : State} {work settled}
    (generated : ReferenceWorkQueue.ExecutedWork work)
    (present : state.queue.RootGroupsPresent)
    (accounted : state.queue.PendingAccounting work settled)
    (keys : state.queue.TaskNodeKeysUnique) (incoming : Occurrence)
    (result : ReferenceWorkQueue.TaskResult) (input : ReferenceWorkQueue.TaskNode)
    (found : state.queue.taskNode? incoming = some input)
    (inputFresh : incoming ∉ settled)
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
    (task : ReferenceWorkQueue.Task) (pending : task.occurrence ∉ incoming :: settled)
    (unrejected
      : state.queue.TaskRejectionsSatisfy (fun rejected _ => rejected ≠ task.occurrence))
    (licensed
      : ∀ occurrence errors,
          (occurrence, errors) ∈ available → occurrence ≠ task.occurrence)
    (evidence
      : SnapshotTaskEvidence
          (registrationSnapshot state.queue (.taskSuccess incoming result)) work)
    (catalogue
      : (registrationSnapshot state.queue (.taskSuccess incoming result)).task?
          task.occurrence
        = some task)
    (links
      : (registrationSnapshot state.queue (.taskSuccess incoming result)).TaskLinkedOn
          task.occurrence (task.groups.map DeliveryNode.ref))
    (owned
      : ∃ owner ∈ task.groups,
          ∃ group,
            (registrationSnapshot state.queue (.taskSuccess incoming result)).groupNode?
              owner.ref
            = some group)
    : RecordTargetRepresented (state.taskSuccess incoming result available).1.queue
        (.task task.occurrence)
      ∨ .abortTask task.occurrence
        ∈ (state.taskSuccess incoming result available).2.2.1 := by
  let stored : State :=
    { state with queue := state.queue.putTaskNode { input with value := some result.value } }
  let integrated := stored.maybeIntegrateWork result.work (some incoming)
  let released := input.task.groups.foldl ReferenceWorkQueue.successGroupStep
    (integrated.1.queue, [], {})
  let starting : State := { integrated.1 with queue := released.1 }
  let active := taskSuccessReadyPhase state incoming result input available
  let referenceReleased := referenceTaskSuccessReleased state.queue incoming result input
  let reference := referenceReleased.1.startNewWork referenceReleased.2.2 available
  have prepared : registrationSnapshot state.queue (.taskSuccess incoming result)
      = integrated.1.queue := by
    simp only [registrationSnapshot, found]
    dsimp only [integrated, stored]
    rw [running]
  rw [prepared] at evidence catalogue links owned
  have debt := state.taskSuccess_registrationDebt present accounted incoming result input
    found inputFresh known
  have uniqueOwners := accounted.matching.contributorsNodup generated
    (accounted.started input (List.mem_of_find?_eq_some found))
  have folded := successGroupFold_unsettledOwners evidence.keys links pending
    input.task.groups uniqueOwners debt
  have foldFrame := ReferenceWorkQueue.State.successGroupFold_noticeTaskProvenance
    evidence.sound evidence.matching input.task.groups
  have afterCatalogue : starting.queue.task? task.occurrence = some task := by
    change released.1.tasks.find? _ = some task
    rw [ReferenceWorkQueue.successGroupFold_tasks]; exact catalogue
  have afterOwned : ∃ owner ∈ task.groups, ∃ group,
      starting.queue.groupNode? owner.ref = some group := by
    obtain ⟨owner, member, group, lookup⟩ := owned
    refine ⟨owner, member, ownerLookup ?_⟩
    exact folded.2.1 owner.ref (List.mem_map_of_mem member)
      (List.mem_map.mpr ⟨group, List.mem_of_find?_eq_some lookup,
        ReferenceWorkQueue.State.groupNode?_ref lookup⟩)
  have storedUnrejected := unrejected.putTaskNode { input with value := some result.value }
    (unrejected input (List.mem_of_find?_eq_some found))
  have integratedUnrejected :=
    State.maybeIntegrateWork_taskRejections (state := stored) storedUnrejected
    result.work (some incoming)
  have afterUnrejected := integratedUnrejected.successGroupFold input.task.groups
  have readyUnrejected : active.1.queue.TaskRejectionsSatisfy
      (fun rejected _ => rejected ≠ task.occurrence) :=
    State.startNewWork_taskRejections afterUnrejected released.2.2 integrated.2 []
      available licensed
  have unique : active.2.2.1.Nodup :=
    State.startNewWork_targets_nodup _ _ _ [] List.nodup_nil available
  have groups : active.1.queue.groupNodes.Sublist released.1.groupNodes :=
    State.startNewWork_groupNodes_sublist_of_matching foldFrame.2 foldFrame.1
      released.2.2 integrated.2 [] available
  have readyBound : active.1.queue.PendingBound (fun _ => True) (incoming :: settled) :=
    fun node member eligible => folded.2.2 node (groups.subset member) eligible
  have readyCatalogue : active.1.queue.task? task.occurrence = some task := by
    change (starting.startNewWork released.2.2 integrated.2 [] available).1.queue.tasks.find? _ = _
    rw [(State.startNewWork_permanentCatalogues starting released.2.2 integrated.2 [] available).1]
    exact afterCatalogue
  have phase := state.taskSuccess_readyCacheProjection generated present accounted keys
    incoming result input found inputFresh known childFresh running available startupFrames
  have exposed := congrArg Prod.fst phase
  change active.1.queue.cacheTaskFailures available = reference.1.cacheTaskFailures available
    at exposed
  have referenceKeys : reference.1.TaskNodeKeysUnique :=
    (((keys.putTaskNode _).maybeIntegrateWork result.work (some incoming)).successGroupFold
      input.task.groups).startNewWork referenceReleased.2.2 available
  have readyKeys : active.1.queue.TaskNodeKeysUnique := by
    have cached := referenceKeys.cacheTaskFailures available
    rw [← exposed] at cached
    simpa only [ReferenceWorkQueue.State.TaskNodeKeysUnique,
      ReferenceWorkQueue.State.cacheTaskFailures_taskOccurrences] using cached
  obtain ⟨parents, owners, forest⟩ := startupFrames
  have readyOwners := ReferenceWorkQueue.State.TaskOwnerFrame.of_cacheTaskFailures_eq
    readyKeys available exposed (owners.startNewWork referenceReleased.2.2 available)
  have readyForest : active.1.queue.RemovalForest parents := by
    have groupEq := congrArg ReferenceWorkQueue.State.groupNodes exposed
    simp only [ReferenceWorkQueue.State.cacheTaskFailures_groupNodes] at groupEq
    apply (forest.startNewWork referenceReleased.2.2 available).of_subset
    rw [groupEq]
    exact List.Subset.refl _
  have readyRunning : active.1.stopped = false :=
    (taskSuccessReadyPhase_stopped state incoming result input available).trans running
  rcases startNewWork_linkedTask_progress_available starting released.2.2 integrated.2 task []
      List.nodup_nil afterCatalogue folded.1 afterOwned afterUnrejected available licensed
      with kept | requested
  · have classified := fusedUnsettledDrainProgress_available task active.2.2.1 readyRunning
      readyOwners readyForest readyCatalogue kept.1 readyBound pending kept.2 unique
      readyUnrejected available licensed
    rw [state.taskSuccess_eq incoming result input found available]
    rcases classified with retained | aborted
    · exact .inl retained
    · exact .inr (List.mem_append_right _ aborted)
  · have finalRequested : .task task.occurrence
        ∈ (active.1.drainReadyGroups active.2.2.1 available).2.2.1 :=
      (State.drainReadyGroups_targets active.1 active.2.2.1 unique available).2.subset requested
    rw [state.taskSuccess_eq incoming result input found available]
    exact .inr (List.mem_append_right _
      (List.mem_flatMap.mpr ⟨.task task.occurrence, finalRequested, List.mem_cons_self⟩))

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
