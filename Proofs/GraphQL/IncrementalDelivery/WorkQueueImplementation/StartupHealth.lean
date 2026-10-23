import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ChildLinks
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.CachedFailures

/-! Healthy registered owners survive startup cleanup driven by supported rejections. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Cache exposure preserves the permanent catalogue and healthy owner records. -/
theorem State.HealthyRegisteredTaskAccounting.cacheTaskFailures
    {queue : State} {work : Execution.Work} {settled failed : List Occurrence}
    (accounted : queue.HealthyRegisteredTaskAccounting work settled failed)
    (available : List (Occurrence × Nat))
    : (queue.cacheTaskFailures available).HealthyRegisteredTaskAccounting work settled
        failed := by
  simpa only [State.HealthyRegisteredTaskAccounting, State.cacheTaskFailures_tasks,
    State.cacheTaskFailures_groupNodes]
    using accounted

/-- A group rejected during startup is invalidated by a recorded contributing task. -/
theorem State.CachedFailuresSupported.startGroup_invalidated {queue : State}
    {work : Execution.Work} {failed : List Occurrence}
    (supported : queue.CachedFailuresSupported work failed)
    (registered : queue.StartedTasksRegistered)
    (tasksMatch : queue.RegisteredTasksMatch work) (sound : queue.GroupMembershipSound)
    {ref : NodeRef} {node : GroupNode} (found : queue.groupNode? ref = some node)
    (nonempty
      : node.tasks.filterMap (fun task => (queue.taskNode? task).bind (·.rejection)) ≠ [])
    : GroupInvalidated work failed node.group.node.ref := by
  obtain ⟨errors, member⟩ := List.exists_mem_of_ne_nil _ nonempty
  obtain ⟨occurrence, listed, rejected⟩ := List.mem_filterMap.mp member
  cases taskFound : queue.taskNode? occurrence with
  | none => simp [taskFound] at rejected
  | some task =>
      have cached : task.rejection = some errors := by simpa [taskFound] using rejected
      have live := List.mem_of_find?_eq_some taskFound
      have same : task.task.occurrence = occurrence :=
        (occurrence_beq_iff_eq _ _).mp (List.find?_some
          (p := fun candidate : TaskNode => candidate.task.occurrence == occurrence) taskFound)
      have owner := sound.startedOwner registered tasksMatch live
        (List.mem_of_find?_eq_some found) (same.symm ▸ listed)
      obtain ⟨group, contributes, equal⟩ := List.mem_map.mp owner
      exact equal ▸ supported.invalidated live (by simp [cached]) contributes

/-- Startup removes only invalidated records when task caches and child edges are supported. -/
theorem State.HealthyRegisteredTaskAccounting.startGroup {queue : State}
    {work : Execution.Work} {settled failed : List Occurrence} {parents : Nat → NodeRefs}
    (accounted : queue.HealthyRegisteredTaskAccounting work settled failed)
    (supported : queue.CachedFailuresSupported work failed)
    (registered : queue.StartedTasksRegistered)
    (tasksMatch : queue.RegisteredTasksMatch work) (sound : queue.GroupMembershipSound)
    (generated : ExecutedWork work) (links : queue.ChildLinksCanonical parents)
    (matching : queue.GroupNodesMatchWork work)
    (canonical
      : ∀ group dependencies,
          GroupRecordAt work group dependencies → dependencies = parents group.ref)
    (ref : NodeRef) (available : List (Occurrence × Nat) := [])
    (recorded
      : ∀ occurrence errors, (occurrence, errors) ∈ available → occurrence ∈ failed := by
        intro occurrence errors member; cases member)
    : (queue.startGroup ref available).1.HealthyRegisteredTaskAccounting work settled
        failed := by
  have tasks (more : List Occurrence) (current : State)
      (valid : current.HealthyRegisteredTaskAccounting work settled failed)
      : (more.foldl (fun current task => current.startTask task available)
          current).HealthyRegisteredTaskAccounting work settled failed := by
    induction more generalizing current with
    | nil => exact valid
    | cons task rest ih =>
        apply ih
        dsimp only
        unfold State.startTask
        split
        · exact valid
        · split <;> exact valid
  have cached := accounted.cacheTaskFailures available
  have supportedCache := supported.cacheTaskFailures registered tasksMatch available recorded
  have registeredCache := registered.cacheTaskFailures available
  have matchingCache := tasksMatch.cacheTaskFailures available
  have soundCache := sound.cacheTaskFailures available
  have linksCache := links.cacheTaskFailures available
  have groupsCache := matching.cacheTaskFailures available
  unfold State.startGroup
  dsimp only
  split
  · exact cached
  · rename_i node found
    split
    · exact tasks _ _ cached
    · rename_i rejected
      have nonempty : node.tasks.filterMap
          (fun task => ((queue.cacheTaskFailures available).taskNode? task).bind (·.rejection))
          ≠ [] := by
        intro empty
        simp only [empty, List.isEmpty_nil] at rejected
        exact rejected trivial
      have invalid := supportedCache.startGroup_invalidated registeredCache matchingCache soundCache
        found nonempty
      exact cached.removeInvalidatedGroup matchingCache generated linksCache groupsCache canonical
        node.group.node.ref invalid.toRecordInvalidated

/-- Activation preserves healthy owners through immediate cached-failure disposal.
The proof threads source provenance and canonical child edges across each group startup.
-/
theorem State.HealthyRegisteredTaskAccounting.startNewWork {queue : State}
    {work : Execution.Work} {settled failed : List Occurrence} {parents : Nat → NodeRefs}
    (accounted : queue.HealthyRegisteredTaskAccounting work settled failed)
    (supported : queue.CachedFailuresSupported work failed)
    (registered : queue.StartedTasksRegistered)
    (tasksMatch : queue.RegisteredTasksMatch work) (sound : queue.GroupMembershipSound)
    (generated : ExecutedWork work) (links : queue.ChildLinksCanonical parents)
    (matching : queue.GroupNodesMatchWork work)
    (canonical
      : ∀ group dependencies,
          GroupRecordAt work group dependencies → dependencies = parents group.ref)
    (more : NewWork) (available : List (Occurrence × Nat) := [])
    (recorded
      : ∀ occurrence errors, (occurrence, errors) ∈ available → occurrence ∈ failed := by
        intro occurrence errors member; cases member)
    : (queue.startNewWork more available).1.HealthyRegisteredTaskAccounting work settled
        failed := by
  let invariant (current : State) :=
    current.HealthyRegisteredTaskAccounting work settled failed ∧
      current.CachedFailuresSupported work failed ∧ current.StartedTasksRegistered ∧
      current.RegisteredTasksMatch work ∧ current.GroupMembershipSound ∧
      current.ChildLinksCanonical parents ∧ current.GroupNodesMatchWork work
  have groupStable (current : State) (ref : NodeRef) (valid : invariant current)
      : invariant (current.startGroup ref available).1 := by
    have sub := (current.startGroup_groupNodes_sublist ref available).subset
    refine ⟨valid.1.startGroup valid.2.1 valid.2.2.1 valid.2.2.2.1 valid.2.2.2.2.1
        generated valid.2.2.2.2.2.1 valid.2.2.2.2.2.2 canonical ref available recorded, ?_,
      valid.2.2.1.startGroup ref available, valid.2.2.2.1.startGroup ref available,
      valid.2.2.2.2.1.startGroup ref available,
      (fun node member => valid.2.2.2.2.2.1 node (sub member)),
      (fun node member => valid.2.2.2.2.2.2 node (sub member))⟩
    exact valid.2.1.startGroup_available valid.2.2.1 valid.2.2.2.1 ref available recorded
  have groups (refs : NodeRefs) (acc : State × List GroupFailureEvent)
      (valid : invariant acc.1)
      : invariant (refs.foldl (fun (current, failures) ref =>
          let (next, queued) := current.startGroup ref available
          (next, failures ++ queued)) acc).1 := by
    induction refs generalizing acc with
    | nil => exact valid
    | cons ref rest ih => exact ih _ (groupStable _ ref valid)
  have streams (refs : NodeRefs) (current : State)
      (valid : current.HealthyRegisteredTaskAccounting work settled failed)
      : (refs.foldl State.startStream current).HealthyRegisteredTaskAccounting
          work settled failed := by
    induction refs generalizing current with
    | nil => exact valid
    | cons ref rest ih =>
        apply ih
        unfold State.startStream
        split <;> exact valid
  unfold State.startNewWork
  exact streams _ _ (groups _ _
    ⟨accounted, supported, registered, tasksMatch, sound, links, matching⟩).1

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
