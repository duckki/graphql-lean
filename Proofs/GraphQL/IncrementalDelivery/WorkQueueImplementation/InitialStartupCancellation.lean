import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.InitialStartupCausality
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.InitialStartupAnnouncements

/-! Initial physical cancellation is backed by the licensed initial causal inventory. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

private theorem startGroup_cancelled_initial {queue : State} {work : Execution.Work}
    {parents : Nat → NodeRefs} {startup : InitialStartup} {initial : NodeRefs}
    (supported
      : queue.CancelledRecordsSupported work
          (InitialStartup.reportingOccurrences startup work initial))
    (rejected
      : queue.TaskRejectionsSatisfy
          (fun occurrence errors => (occurrence, errors) ∈ startup.failures))
    (sound : queue.GroupMembershipSound) (tasks : queue.RegisteredTasksMatch work)
    (groups : queue.GroupNodesMatchWork work) (links : queue.ChildLinksCanonical parents)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (ref : NodeRef) (announced : ref ∈ initial)
    : (queue.startGroup ref startup.failures).1.CancelledRecordsSupported work
        (startup.reportingOccurrences work initial) := by
  let cached := queue.cacheTaskFailures startup.failures
  have supportedCache : cached.CancelledRecordsSupported work
      (startup.reportingOccurrences work initial) := by
    intro key member
    rw [State.cacheTaskFailures_cancelledGroups] at member
    exact supported key member
  have cachedRejections := rejected.cacheTaskFailures startup.failures (fun _ _ member => member)
  have cachedSound := sound.cacheTaskFailures startup.failures
  have cachedTasks := tasks.cacheTaskFailures startup.failures
  have starts (more : List Occurrence) (current : State)
      (valid : current.CancelledRecordsSupported work (startup.reportingOccurrences work initial))
      : (more.foldl (fun state task => state.startTask task startup.failures)
          current).CancelledRecordsSupported work (startup.reportingOccurrences work initial) := by
    induction more generalizing current with
    | nil => exact valid
    | cons task rest ih =>
        apply ih
        dsimp only
        unfold State.startTask
        split
        · exact valid
        · split <;> exact valid
  unfold State.startGroup
  dsimp only
  split
  · exact supportedCache
  · rename_i node found
    split
    · exact starts _ _ supportedCache
    · rename_i rejectedGroup
      have nonempty : cached.cachedTaskCauses node.tasks ≠ [] := by
        intro empty
        apply rejectedGroup
        change (node.tasks.filterMap
          (fun task => (cached.taskNode? task).bind (·.rejection))).isEmpty = true
        rw [← cached.cachedTaskCauses_errors node.tasks, empty]
        rfl
      obtain ⟨cause, member⟩ := List.exists_mem_of_ne_nil _ nonempty
      have listed := (cached.cachedTaskCauses_tasks node.tasks).subset (List.mem_map_of_mem member)
      have available := cachedRejections.cachedTaskCauses node.tasks cause member
      obtain ⟨task, registered, identity, contributes⟩ :=
        cachedSound node (List.mem_of_find?_eq_some found) cause.1 listed
      obtain ⟨address, payload, producer, shape, known⟩ := (cachedTasks task registered).1
      have reported : task.occurrence ∈ startup.reportingOccurrences work initial := by
        apply InitialStartup.mem_reportingOccurrences.mpr
        refine ⟨?_, task.groups.map Execution.DeliveryNode.ref, ⟨producer, payload, known⟩,
          node.group.node.ref, contributes, ?_⟩
        · rw [identity]
          exact List.mem_map_of_mem available
        · rwa [State.groupNode?_ref found]
      exact supportedCache.removeGroup (links.cacheTaskFailures startup.failures)
        (groups.cacheTaskFailures startup.failures) canonical node.group.node.ref
        (.task ⟨producer, payload, known⟩ contributes reported)

private theorem startNewWork_cancelled_initial {queue : State} {work : Execution.Work}
    {parents : Nat → NodeRefs} {startup : InitialStartup} {initial : NodeRefs}
    (supported
      : queue.CancelledRecordsSupported work
          (InitialStartup.reportingOccurrences startup work initial))
    (rejected
      : queue.TaskRejectionsSatisfy
          (fun occurrence errors => (occurrence, errors) ∈ startup.failures))
    (sound : queue.GroupMembershipSound) (tasks : queue.RegisteredTasksMatch work)
    (groups : queue.GroupNodesMatchWork work) (links : queue.ChildLinksCanonical parents)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (released : NewWork)
    (announced : (released.newGroups.map Execution.DeliveryNode.ref).Subset initial)
    : (queue.startNewWork released startup.failures).1.CancelledRecordsSupported work
        (startup.reportingOccurrences work initial) := by
  let invariant (current : State) := current.CancelledRecordsSupported work
      (startup.reportingOccurrences work initial)
    ∧ current.TaskRejectionsSatisfy
        (fun occurrence errors => (occurrence, errors) ∈ startup.failures)
    ∧ current.GroupMembershipSound ∧ current.RegisteredTasksMatch work
    ∧ current.GroupNodesMatchWork work ∧ current.ChildLinksCanonical parents
  have loop (refs : NodeRefs) (included : refs.Subset initial)
      (acc : State × List GroupFailureEvent) (prior : invariant acc.1)
      : invariant (refs.foldl (fun (current, failures) ref =>
          let next := current.startGroup ref startup.failures
          (next.1, failures ++ next.2)) acc).1 := by
    induction refs generalizing acc with
    | nil => exact prior
    | cons ref rest ih =>
        apply ih (fun _ member => included (List.mem_cons_of_mem _ member))
        exact ⟨startGroup_cancelled_initial prior.1 prior.2.1 prior.2.2.1 prior.2.2.2.1
            prior.2.2.2.2.1 prior.2.2.2.2.2 canonical ref (included List.mem_cons_self),
          prior.2.1.startGroup ref startup.failures (fun _ _ member => member),
          prior.2.2.1.startGroup ref startup.failures,
          prior.2.2.2.1.startGroup ref startup.failures,
          fun node member => prior.2.2.2.2.1 node
            ((acc.1.startGroup_groupNodes_sublist ref startup.failures).subset member),
          fun node member => prior.2.2.2.2.2 node
            ((acc.1.startGroup_groupNodes_sublist ref startup.failures).subset member)⟩
  have grouped := loop (released.newGroups.map Execution.DeliveryNode.ref) announced
    ({queue with rootGroups := queue.rootGroups ++
      released.newGroups.map Execution.DeliveryNode.ref}, [])
    ⟨supported, rejected, sound, tasks, groups, links⟩
  have streams (refs : NodeRefs) (current : State)
      (prior : current.CancelledRecordsSupported work (startup.reportingOccurrences work initial))
      : (refs.foldl State.startStream current).CancelledRecordsSupported work
          (startup.reportingOccurrences work initial) := by
    induction refs generalizing current with
    | nil => exact prior
    | cons ref rest ih =>
        apply ih
        unfold State.startStream
        split <;> exact prior
  exact streams _ _ grouped.1

/-- Every initial cancellation marker has a cause in the initial reporting inventory.
Only rejected tasks actually inspected at an announced root license cancellation.
Unused synchronous observations of dormant tasks add no cancellation premise.
-/
theorem State.initializeWithStartup_cancelled_supported {work : Execution.Work}
    {parents : Nat → NodeRefs} (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (startup : InitialStartup)
    : let initialized := State.initialize (Work.fromExecution work) startup
      let initial :=
        (initialized.initialGroups ++ initialized.initialStreams).map
          Execution.DeliveryNode.ref
      initialized.CancelledRecordsSupported work
        (startup.reportingOccurrences work initial) := by
  let prepared := initialPreparation work
  have parent := initialPreparation_parentCutFrame generated canonical
  have owners := initialPreparation_taskOwnerFrame work
  have empty : ({} : State).TaskRejectionsSatisfy
      (fun occurrence errors => (occurrence, errors) ∈ startup.failures) := by
    intro node member; cases member
  have rejected := (empty.maybeIntegrateWork (Work.fromExecution work)).pruneEmptyGroups
    (({} : State).maybeIntegrateWork (Work.fromExecution work)).2.newGroups
  dsimp only
  rw [State.initializeWithStartup_eq_preparation]
  refine startNewWork_cancelled_initial ?_ rejected owners.sound owners.matching
    parent.records parent.links canonical prepared.2 ?_
  · intro ref member
    change ref ∈ (initialPreparation work).1.cancelledGroups at member
    rw [initialPreparation_cancelledGroups_empty] at member
    cases member
  · intro ref member
    rw [List.map_append]
    exact List.mem_append_left _ member

/-- Actual initial removal is supported by the licensed selected causal failures. -/
theorem State.initializeWithStartup_cancelled_causal {work : Execution.Work}
    {parents : Nat → NodeRefs} (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (startup : InitialStartup)
    : let initialized := State.initialize (Work.fromExecution work) startup
      let initial :=
        (initialized.initialGroups ++ initialized.initialStreams).map
          Execution.DeliveryNode.ref
      initialized.CancelledRecordsSupported work
        ((startup.causalCuts work initial).map Prod.snd) := by
  have supported := State.initializeWithStartup_cancelled_supported generated canonical startup
  dsimp only at supported ⊢
  intro ref member
  exact (startup.causalCuts_groupRecordInvalidated work _ ref).mp (supported ref member)

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
