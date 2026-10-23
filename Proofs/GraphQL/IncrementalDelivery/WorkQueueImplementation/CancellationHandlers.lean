import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.CancellationPreservation
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupHealth
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.CacheEligibility

/-! Source support for cancellation written by task dispatch and cached-failure startup. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (StreamItemValue WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Task retirement leaves the permanent cancellation inventory unchanged. -/
theorem State.CancelledRecordsSupported.removeTask {queue work failed}
    (supported : State.CancelledRecordsSupported queue work failed) (task : Occurrence)
    : (queue.removeTask task).CancelledRecordsSupported work failed :=
  supported

/-- Failure-owner cleanup writes only cancellation refs supported by recorded tasks. -/
private theorem State.CancelledRecordsSupported.taskFailure_of_causes
    {queue work parents failed}
    (supported : State.CancelledRecordsSupported queue work failed)
    (matching : queue.GroupNodesMatchWork work)
    (links : queue.ChildLinksCanonical parents)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (occurrence : Occurrence) (errors : Nat)
    (causes
      : ∀ node,
          queue.taskNode? occurrence = some node
          → ∀ group ∈ node.task.groups,
              ∃ task ∈ failed,
                ∃ owners, TaskHasOwners work task owners ∧ group.ref ∈ owners)
    : (queue.taskFailure occurrence errors).1.CancelledRecordsSupported work failed := by
  cases found : queue.taskNode? occurrence with
  | none => simpa [State.taskFailure, found] using supported
  | some node =>
      rw [queue.taskFailure_eq occurrence errors node found]
      let invariant (state : State) := state.CancelledRecordsSupported work failed
        ∧ state.GroupNodesMatchWork work ∧ state.ChildLinksCanonical parents
      have permitted (group : Execution.DeliveryNode) (member : group ∈ node.task.groups)
          : GroupRecordInvalidated work failed group.ref := by
        obtain ⟨task, recorded, owners, known, owner⟩ := causes node found group member
        exact (GroupInvalidated.task known owner recorded).toRecordInvalidated
      have final := failureGroupFold_preserves_on invariant (GroupRecordInvalidated work failed)
        (fun state ref prior invalidated =>
          ⟨prior.1.removeGroup prior.2.2 prior.2.1 canonical ref invalidated,
            prior.2.1.removeGroup ref, prior.2.2.removeGroup ref⟩)
        errors node.task.groups permitted
        (queue.putTaskNode { node with rejection := some errors }, [])
        ⟨supported, matching, links⟩
      exact final.1

/-- Failed-task handling preserves support using the actual started task's contributors.
Witness: task provenance licenses each removed owner; canonical edges license descendants.
Ignored or missing tasks retain the old registry without using the recorded-failure premise.
-/
theorem State.CancelledRecordsSupported.taskFailure {queue work parents failed}
    (supported : State.CancelledRecordsSupported queue work failed)
    (registered : queue.StartedTasksRegistered)
    (tasksMatch : queue.RegisteredTasksMatch work)
    (matching : queue.GroupNodesMatchWork work)
    (links : queue.ChildLinksCanonical parents)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (occurrence : Occurrence) (errors : Nat)
    (recorded : ∀ node, queue.taskNode? occurrence = some node → occurrence ∈ failed)
    : (queue.taskFailure occurrence errors).1.CancelledRecordsSupported work failed := by
  apply supported.taskFailure_of_causes matching links canonical occurrence errors
  intro node found group contributes
  have same : node.task.occurrence = occurrence :=
    (occurrence_beq_iff_eq _ _).mp
      (List.find?_some
        (p := fun candidate : TaskNode => candidate.task.occurrence == occurrence) found)
  obtain ⟨address, payload, producer, _, known⟩ :=
    (tasksMatch node.task (registered node (List.mem_of_find?_eq_some found))).1
  exact ⟨occurrence, recorded node found, _, ⟨producer, payload, same ▸ known⟩,
    List.mem_map.mpr ⟨group, contributes, rfl⟩⟩

/-- Successful closure retains existing cancellation witnesses. -/
theorem State.CancelledRecordsSupported.finishGroupSuccess {queue work failed}
    (supported : State.CancelledRecordsSupported queue work failed) (node : GroupNode)
    : (queue.finishGroupSuccess node).1.CancelledRecordsSupported work failed := by
  intro ref member
  rw [State.finishGroupSuccess_cancelledGroups] at member
  exact supported ref member

/-- Startup cancellation is licensed by a cached contributing rejection. -/
theorem State.CancelledRecordsSupported.startGroup {queue work parents failed}
    (supported : State.CancelledRecordsSupported queue work failed)
    (cached : queue.CachedFailuresSupported work failed)
    (registered : queue.StartedTasksRegistered) (tasks : queue.RegisteredTasksMatch work)
    (sound : queue.GroupMembershipSound) (matching : queue.GroupNodesMatchWork work)
    (links : queue.ChildLinksCanonical parents)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (ref : NodeRef)
    (available : List (Occurrence × Nat) := [])
    (availableRecorded
      : ∀ occurrence errors, (occurrence, errors) ∈ available → occurrence ∈ failed := by
        intro occurrence errors member; cases member)
    : (queue.startGroup ref available).1.CancelledRecordsSupported work failed := by
  have starts (more : List Occurrence) (current : State)
      (valid : current.CancelledRecordsSupported work failed)
      : (more.foldl (fun current task => current.startTask task available)
          current).CancelledRecordsSupported work failed := by
    induction more generalizing current with
    | nil => exact valid
    | cons task rest ih =>
        apply ih
        dsimp only
        unfold State.startTask
        split
        · exact valid
        · split <;> exact valid
  have cancelledCache : (queue.cacheTaskFailures
      available).CancelledRecordsSupported work failed := by
    intro key member
    rw [State.cacheTaskFailures_cancelledGroups] at member
    exact supported key member
  have supportedCache := cached.cacheTaskFailures registered tasks available availableRecorded
  have registeredCache := registered.cacheTaskFailures available
  have tasksCache := tasks.cacheTaskFailures available
  have soundCache := sound.cacheTaskFailures available
  have matchingCache := matching.cacheTaskFailures available
  have linksCache := links.cacheTaskFailures available
  unfold State.startGroup
  dsimp only
  split
  · exact cancelledCache
  · rename_i node found
    split
    · exact starts _ _ cancelledCache
    · rename_i rejected
      have nonempty : node.tasks.filterMap
          (fun task => ((queue.cacheTaskFailures available).taskNode? task).bind (·.rejection))
          ≠ [] := by
        intro empty
        simp only [empty, List.isEmpty_nil] at rejected
        exact rejected trivial
      have invalid := supportedCache.startGroup_invalidated registeredCache tasksCache soundCache
        found nonempty
      exact cancelledCache.removeGroup linksCache matchingCache canonical node.group.node.ref
        invalid.toRecordInvalidated

/-- Internal provenance retained between integrations and startup disposal. -/
private structure State.CancellationContext (queue : State) (work : Execution.Work)
    (parents : Nat → NodeRefs) (failed : List Occurrence)
    : Prop where
  cancelled : queue.CancelledRecordsSupported work failed
  cached : queue.CachedFailuresSupported work failed
  groups : queue.GroupNodesMatchWork work
  links : queue.ChildLinksCanonical parents
  registered : queue.StartedTasksRegistered
  tasks : queue.RegisteredTasksMatch work
  sound : queue.GroupMembershipSound

private theorem State.CancellationContext.finishGroupSuccess {queue work parents failed}
    (valid : State.CancellationContext queue work parents failed) (node : GroupNode)
    : (queue.finishGroupSuccess node).1.CancellationContext work parents failed :=
  ⟨
    valid.cancelled.finishGroupSuccess node,
    valid.cached.finishGroupSuccess node,
    valid.groups.finishGroupSuccess node,
    valid.links.finishGroupSuccess node,
    valid.registered.finishGroupSuccess node,
    valid.tasks.finishGroupSuccess node,
    valid.sound.finishGroupSuccess node
  ⟩

private theorem State.CancellationContext.startNewWork {queue work parents failed}
    (valid : State.CancellationContext queue work parents failed) (more : NewWork)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (available : List (Occurrence × Nat) := [])
    (availableRecorded
      : ∀ occurrence errors, (occurrence, errors) ∈ available → occurrence ∈ failed := by
        intro occurrence errors member; cases member)
    : (queue.startNewWork more available).1.CancellationContext work parents failed := by
  have stable (current : State) (ref : NodeRef)
      (prior : current.CancellationContext work parents failed)
      : (current.startGroup ref available).1.CancellationContext work parents failed := by
    have sub := (current.startGroup_groupNodes_sublist ref available).subset
    exact ⟨prior.cancelled.startGroup prior.cached prior.registered prior.tasks prior.sound
        prior.groups prior.links canonical ref available availableRecorded,
      prior.cached.startGroup_available prior.registered prior.tasks ref available
        availableRecorded,
      (fun node member => prior.groups node (sub member)),
      (fun node member => prior.links node (sub member)),
      prior.registered.startGroup ref available, prior.tasks.startGroup ref available,
      prior.sound.startGroup ref available⟩
  have groups (refs : NodeRefs) (acc : State × List GroupFailureEvent)
      (prior : acc.1.CancellationContext work parents failed)
      : (refs.foldl (fun (current, failures) ref =>
          let (next, queued) := current.startGroup ref available
          (next, failures ++ queued)) acc).1.CancellationContext work parents failed := by
    induction refs generalizing acc with
    | nil => exact prior
    | cons ref rest ih => exact ih _ (stable _ ref prior)
  have streams (refs : NodeRefs) (current : State)
      (prior : current.CancellationContext work parents failed)
      : (refs.foldl State.startStream current).CancellationContext work parents failed := by
    induction refs generalizing current with
    | nil => exact prior
    | cons ref rest ih =>
        apply ih
        unfold State.startStream
        split
        · exact prior
        · exact ⟨prior.cancelled, prior.cached, prior.groups, prior.links,
            prior.registered, prior.tasks, prior.sound⟩
  unfold State.startNewWork
  exact streams _ _ (groups _ _ ⟨valid.cancelled, valid.cached, valid.groups, valid.links,
    valid.registered, valid.tasks, valid.sound⟩)

/-- Activation may append cancellations, each supported by a cached task cause. -/
theorem State.CancelledRecordsSupported.startNewWork {queue work parents failed}
    (supported : State.CancelledRecordsSupported queue work failed)
    (cached : queue.CachedFailuresSupported work failed)
    (registered : queue.StartedTasksRegistered) (tasks : queue.RegisteredTasksMatch work)
    (sound : queue.GroupMembershipSound) (matching : queue.GroupNodesMatchWork work)
    (links : queue.ChildLinksCanonical parents)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (more : NewWork)
    (available : List (Occurrence × Nat) := [])
    (availableRecorded
      : ∀ occurrence errors, (occurrence, errors) ∈ available → occurrence ∈ failed := by
        intro occurrence errors member; cases member)
    : (queue.startNewWork more available).1.CancelledRecordsSupported work failed :=
  (State.CancellationContext.startNewWork
    ⟨supported, cached, matching, links, registered, tasks, sound⟩ more
    canonical available availableRecorded).cancelled

/-- Recursive successful draining retains supported cancellation history through startup. -/
theorem State.CancelledRecordsSupported.drainReadyGroups {queue work parents failed}
    (supported : State.CancelledRecordsSupported queue work failed)
    (cached : queue.CachedFailuresSupported work failed)
    (matching : queue.GroupNodesMatchWork work)
    (links : queue.ChildLinksCanonical parents)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (registered : queue.StartedTasksRegistered) (tasks : queue.RegisteredTasksMatch work)
    (sound : queue.GroupMembershipSound)
    (available : List (Occurrence × Nat) := [])
    (availableRecorded
      : ∀ occurrence errors, (occurrence, errors) ∈ available → occurrence ∈ failed := by
        intro occurrence errors member; cases member)
    : (queue.drainReadyGroups available).1.CancelledRecordsSupported work failed := by
  have final := State.drainReadyGroups_preserves
    (fun current => current.CancellationContext work parents failed) (available := available)
    (fun _ node prior _ _ _ => (prior.finishGroupSuccess node).startNewWork
      _ canonical available availableRecorded)
    (show queue.CancellationContext work parents failed from
      ⟨supported, cached, matching, links, registered, tasks, sound⟩)
  exact final.cancelled

private theorem State.CancellationContext.maybeIntegrateWork {queue work parents failed}
    (valid : State.CancellationContext queue work parents failed) (more : Work)
    (producer : Option Occurrence)
    (descriptors
      : ∀ group ∈ more.groups,
          ∃ dependencies,
            GroupRecordAt work group.node dependencies
            ∧ group.parent = dependencies.head?)
    (knownTasks : ∀ task ∈ more.tasks, TaskMatches work task)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    : (queue.maybeIntegrateWork more producer).1.CancellationContext work parents
        failed := by
  refine ⟨valid.cancelled.maybeIntegrateWork more producer descriptors,
    valid.cached.maybeIntegrateWork more producer,
    valid.groups.maybeIntegrateWork more ?_ producer,
    valid.links.maybeIntegrateWork more ?_ producer,
    valid.registered.maybeIntegrateWork more producer,
    valid.tasks.maybeIntegrateWork more knownTasks producer,
    valid.sound.maybeIntegrateWork more producer⟩
  · intro group member
    obtain ⟨dependencies, known, _⟩ := descriptors group member
    exact ⟨dependencies, known⟩
  · intro group member
    obtain ⟨dependencies, known, parent⟩ := descriptors group member
    rw [parent, canonical group.node dependencies known]

private theorem State.CancellationContext.pruneEmptyGroups {queue work parents failed}
    (valid : State.CancellationContext queue work parents failed)
    (groups : List Execution.DeliveryNode)
    : (queue.pruneEmptyGroups groups).1.CancellationContext work parents failed := by
  refine ⟨?_, valid.cached.pruneEmptyGroups groups, valid.groups.pruneEmptyGroups groups,
    valid.links.pruneEmptyGroups groups, valid.registered.pruneEmptyGroups groups,
    valid.tasks.pruneEmptyGroups groups, valid.sound.pruneEmptyGroups groups⟩
  intro ref member
  rw [State.pruneEmptyGroups_cancelledGroups] at member
  exact valid.cancelled ref member

/-- Successful settlement preserves support even when it releases an older cached failure.
Witness: child registration and the single-pass success loop preserve the local facts;
the final drain attributes newly cancelled groups to their retained failure causes. -/
theorem State.CancelledRecordsSupported.taskSuccess {queue work parents failed}
    (supported : State.CancelledRecordsSupported queue work failed)
    (cached : queue.CachedFailuresSupported work failed)
    (matching : queue.GroupNodesMatchWork work)
    (links : queue.ChildLinksCanonical parents)
    (registered : queue.StartedTasksRegistered)
    (tasksMatch : queue.RegisteredTasksMatch work) (sound : queue.GroupMembershipSound)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (occurrence : Occurrence) (result : TaskResult)
    (descriptors
      : ∀ group ∈ result.work.groups,
          ∃ dependencies,
            GroupRecordAt work group.node dependencies
            ∧ group.parent = dependencies.head?)
    (knownTasks : ∀ task ∈ result.work.tasks, TaskMatches work task)
    (available : List (Occurrence × Nat) := [])
    (availableRecorded
      : ∀ occurrence errors, (occurrence, errors) ∈ available → occurrence ∈ failed := by
        intro occurrence errors member; cases member)
    : (queue.taskSuccess occurrence result available).1.CancelledRecordsSupported work
        failed := by
  have step (acc : State × List WorkQueueEvent × NewWork) (group : Execution.DeliveryNode)
      (valid : acc.1.CancellationContext work parents failed)
      : (successGroupStep acc group).1.CancellationContext work parents failed := by
    obtain ⟨current, events, released⟩ := acc
    dsimp only [successGroupStep]
    split
    · exact valid
    · rename_i node found
      have member := List.mem_of_find?_eq_some found
      have updated : State.CancellationContext
          (current.putGroupNode { node with pending := node.pending - 1 }) work parents failed :=
        ⟨valid.cancelled, valid.cached.putGroupNode _,
          valid.groups.putGroupNode _ (valid.groups node member),
          valid.links.putGroupNode _ (valid.links node member),
          valid.registered.putGroupNode _, valid.tasks.putGroupNode _,
          valid.sound.putGroupNode _ (valid.sound node member)⟩
      split
      · exact updated.finishGroupSuccess _
      · exact updated
  have fold (groups : List Execution.DeliveryNode)
      (acc : State × List WorkQueueEvent × NewWork)
      (valid : acc.1.CancellationContext work parents failed)
      : (groups.foldl successGroupStep acc).1.CancellationContext work parents
          failed := by
    induction groups generalizing acc with
    | nil => exact valid
    | cons group rest ih => exact ih _ (step acc group valid)
  unfold State.taskSuccess
  split
  · exact supported
  · rename_i taskNode found
    let withValue := queue.putTaskNode { taskNode with value := some result.value }
    have before : withValue.CancellationContext work parents failed :=
      ⟨supported, State.CachedErrorsSatisfy.putTaskNode cached _
        (cached taskNode (List.mem_of_find?_eq_some found)), matching, links,
        registered.putTaskNode _ (registered taskNode (List.mem_of_find?_eq_some found)),
        tasksMatch, sound⟩
    have integrated := before.maybeIntegrateWork result.work (some occurrence)
      descriptors knownTasks canonical
    have released := fold taskNode.task.groups
      ((withValue.maybeIntegrateWork result.work (some occurrence)).1, [], {}) integrated
    have started := released.startNewWork
      (taskNode.task.groups.foldl successGroupStep
        ((withValue.maybeIntegrateWork result.work (some occurrence)).1, [], {})).2.2 canonical
      available availableRecorded
    exact started.cancelled.drainReadyGroups started.cached started.groups started.links canonical
      started.registered started.tasks started.sound available availableRecorded

/-- Item batches preserve support through integration, activation, and retained failures.
Witness: each matched child chunk preserves the same context before the final drain. -/
theorem State.CancelledRecordsSupported.streamItems {queue work parents failed}
    (supported : State.CancelledRecordsSupported queue work failed)
    (cached : queue.CachedFailuresSupported work failed)
    (matching : queue.GroupNodesMatchWork work)
    (links : queue.ChildLinksCanonical parents)
    (registered : queue.StartedTasksRegistered)
    (tasksMatch : queue.RegisteredTasksMatch work) (sound : queue.GroupMembershipSound)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (stream : Execution.DeliveryNode) (items : List StreamItem)
    (descriptors
      : ∀ item ∈ items,
        ∀ group ∈ item.work.groups,
          ∃ dependencies,
            GroupRecordAt work group.node dependencies
            ∧ group.parent = dependencies.head?)
    (knownTasks : ∀ item ∈ items, ∀ task ∈ item.work.tasks, TaskMatches work task)
    (available : List (Occurrence × Nat) := [])
    (availableRecorded
      : ∀ occurrence errors, (occurrence, errors) ∈ available → occurrence ∈ failed := by
        intro occurrence errors member; cases member)
    : (queue.streamItems stream items available).1.CancelledRecordsSupported work
        failed := by
  let step (acc : State × List Execution.DeliveryNode × List Execution.DeliveryNode
      × List StreamItemValue × List GroupFailureEvent) (item : StreamItem) :=
    let (current, groups, streams, values, failures) := acc
    let (integrated, more) := current.maybeIntegrateWork item.work
    let (pruned, nonempty) := integrated.pruneEmptyGroups more.newGroups
    let (started, queued) := pruned.startNewWork { more with newGroups := nonempty } available
    (started, groups ++ nonempty, streams ++ more.newStreams,
      values ++ [item.value], failures ++ queued)
  have fold (more : List StreamItem) (included : more.Subset items)
      (acc : State × List Execution.DeliveryNode × List Execution.DeliveryNode
        × List StreamItemValue × List GroupFailureEvent)
      (valid : acc.1.CancellationContext work parents failed)
      : (more.foldl step acc).1.CancellationContext work parents failed := by
    induction more generalizing acc with
    | nil => exact valid
    | cons item rest ih =>
        apply ih (fun _ member => included (List.mem_cons_of_mem _ member))
        have integrated := valid.maybeIntegrateWork item.work none
          (descriptors item (included List.mem_cons_self))
          (knownTasks item (included List.mem_cons_self)) canonical
        exact (integrated.pruneEmptyGroups _).startNewWork _ canonical available availableRecorded
  unfold State.streamItems
  split
  · exact supported
  · have final := fold items (List.Subset.refl _) (queue, [], [], [], [])
      ⟨supported, cached, matching, links, registered, tasksMatch, sound⟩
    exact final.cancelled.drainReadyGroups final.cached final.groups final.links canonical
      final.registered final.tasks final.sound available availableRecorded

-----------------------------------------------------------------------------------------
-- The source's structural matching discharges child-registration metadata
-----------------------------------------------------------------------------------------

/-- Every matched host event preserves cancellation support when accepted failures are known.
Witness: source matching supplies child descriptors; each task/stream handler then applies
its local preservation theorem. This assumes no admitted output history. -/
theorem State.CancelledRecordsSupported.handleGraphEvent {queue work parents failed}
    (supported : State.CancelledRecordsSupported queue work failed)
    (cached : queue.CachedFailuresSupported work failed)
    (registered : queue.StartedTasksRegistered)
    (tasksMatch : queue.RegisteredTasksMatch work)
    (matching : queue.GroupNodesMatchWork work)
    (links : queue.ChildLinksCanonical parents)
    (sound : queue.GroupMembershipSound)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (event : GraphEvent) (source : event.MatchesWork work)
    (recorded
      : ∀ occurrence errors,
          event = .taskFailure occurrence errors
          → ∀ node, queue.taskNode? occurrence = some node → occurrence ∈ failed)
    (available : List (Occurrence × Nat) := [])
    (availableRecorded
      : ∀ occurrence errors, (occurrence, errors) ∈ available → occurrence ∈ failed := by
        intro occurrence errors member; cases member)
    : (queue.handleGraphEvent event available).1.CancelledRecordsSupported work
        failed := by
  let current := queue.cacheTaskFailures available
  have cancelledCache : current.CancelledRecordsSupported work failed := by
    intro ref member
    rw [State.cacheTaskFailures_cancelledGroups] at member
    exact supported ref member
  have cachedCache := cached.cacheTaskFailures registered tasksMatch available availableRecorded
  have registeredCache := registered.cacheTaskFailures available
  have tasksCache := tasksMatch.cacheTaskFailures available
  have matchingCache := matching.cacheTaskFailures available
  have linksCache := links.cacheTaskFailures available
  have soundCache := sound.cacheTaskFailures available
  have recordedCache : ∀ occurrence errors, event = .taskFailure occurrence errors →
      ∀ node, current.taskNode? occurrence = some node → occurrence ∈ failed := by
    intro occurrence errors same node found
    change (queue.cacheTaskFailures available).taskNode? occurrence = some node at found
    have present : (queue.taskNode? occurrence).isSome = true := by
      have unchanged := queue.cacheTaskFailures_acceptsGraphEvent
        available (.taskFailure occurrence errors)
      simpa only [State.acceptsGraphEvent, found, Option.isSome_some] using unchanged.symm
    cases original : queue.taskNode? occurrence with
    | none => simp [original] at present
    | some old => exact recorded occurrence errors same old original
  cases event with
  | taskSuccess occurrence result =>
      apply cancelledCache.taskSuccess cachedCache matchingCache linksCache
        registeredCache tasksCache
        soundCache canonical occurrence result (available := available)
        (availableRecorded := availableRecorded)
      · intro group member
        obtain ⟨dependencies, known⟩ := source.taskChildGroups_recordAt member
        refine ⟨dependencies, known, ?_⟩
        rw [canonical group.node dependencies known]
        exact source.taskChildGroups_parentCanonical canonical member
      · intro task member
        obtain ⟨address, payload, same, known⟩ := source.childTask_producer member
        exact ⟨⟨address, payload, some occurrence, same, known⟩,
          source.childTask_groupsExact member⟩
  | groupFailure failure =>
      change (current.groupFailure failure).1.CancelledRecordsSupported work failed
      unfold State.groupFailure
      split
      · exact cancelledCache
      · split <;> exact cancelledCache
  | taskFailure occurrence errors =>
      exact cancelledCache.taskFailure registeredCache tasksCache matchingCache linksCache canonical
        occurrence errors (recordedCache occurrence errors rfl)
  | streamItems stream items =>
      apply cancelledCache.streamItems cachedCache matchingCache linksCache
        registeredCache tasksCache
        soundCache canonical stream items (available := available)
        (availableRecorded := availableRecorded)
      · intro item itemMember group member
        obtain ⟨dependencies, known⟩ := source.streamItem_childGroups_recordAt itemMember member
        refine ⟨dependencies, known, ?_⟩
        rw [canonical group.node dependencies known]
        exact source.streamItem_childGroups_parentCanonical canonical itemMember member
      · intro item itemMember task member
        obtain ⟨address, payload, same, known⟩ :=
          source.streamItem_childTask_producer itemMember member
        exact ⟨⟨address, payload, some item.occurrence, same, known⟩,
          source.streamItem_childTask_groupsExact itemMember member⟩
  | streamSuccess stream =>
      change (current.streamSuccess stream).1.CancelledRecordsSupported work failed
      unfold State.streamSuccess
      split <;> exact cancelledCache
  | streamFailure stream errors =>
      change (current.streamFailure stream errors).1.CancelledRecordsSupported work failed
      unfold State.streamFailure
      split <;> exact cancelledCache

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
