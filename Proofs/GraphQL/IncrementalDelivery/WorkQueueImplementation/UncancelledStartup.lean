import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.UncancelledMarkers
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupStartup

/-! Early cached-failure startup preserves ancestor cancellation-marker certificates. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Task startup changes neither group retirements nor cancellation markers. -/
theorem State.UncancelledRetiredMarkers.startTask {queue : State} {work}
    (prior : queue.UncancelledRetiredMarkers work) (occurrence : Occurrence)
    (available : List (Occurrence × Nat) := [])
    : (queue.startTask occurrence available).UncancelledRetiredMarkers work := by
  unfold State.startTask
  split
  · exact prior
  · split <;> exact prior

/-- Cached rejection startup preserves uncancelled retired ancestor markers.
Witness: a nonempty local error collection selects a fresh contributing task. Its owner
licenses immediate removal without consuming or inventing a failure notification.
-/
theorem State.UncancelledRetiredMarkers.startGroup {queue : State}
    {work parents settled}
    (prior : queue.UncancelledRetiredMarkers work)
    (structural : queue.UncancelledRetiredAncestors work)
    (accounted : queue.UncancelledTaskAccounting settled) (generated : ExecutedWork work)
    (links : queue.ChildLinksCanonical parents) (records : queue.GroupNodesMatchWork work)
    (sound : queue.GroupMembershipSound) (matching : queue.RegisteredTasksMatch work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (rejections : queue.TaskRejectionsSatisfy (fun occurrence _ => occurrence ∉ settled))
    (ref : NodeRef) (available : List (Occurrence × Nat))
    (licensed
      : ∀ occurrence errors, (occurrence, errors) ∈ available → occurrence ∉ settled)
    : (queue.startGroup ref available).1.UncancelledRetiredMarkers work := by
  let cached := queue.cacheTaskFailures available
  have markers := prior.cacheTaskFailures available
  have fresh := rejections.cacheTaskFailures available licensed
  have cachedSound := sound.cacheTaskFailures available
  have cachedMatching := matching.cacheTaskFailures available
  unfold State.startGroup
  dsimp only
  split
  · exact markers
  · rename_i node found
    split
    · have fold (tasks : List Occurrence) (current : State)
          (frame : current.UncancelledRetiredMarkers work)
          : (tasks.foldl (fun next task => next.startTask task available)
              current).UncancelledRetiredMarkers work := by
        induction tasks generalizing current with
        | nil => exact frame
        | cons task rest ih => exact ih _ (frame.startTask task available)
      exact fold node.tasks _ markers
    · rename_i nonempty
      have existsCause : ∃ count, count ∈ node.tasks.filterMap
          (fun task => (cached.taskNode? task).bind (·.rejection)) := by
        cases values
              : node.tasks.filterMap
                  (fun task => (cached.taskNode? task).bind (·.rejection)) with
        | nil =>
            apply False.elim
            apply nonempty
            change (node.tasks.filterMap
              (fun task => (cached.taskNode? task).bind (·.rejection))).isEmpty = true
            rw [values]
            rfl
        | cons count rest => exact ⟨count, List.mem_cons_self⟩
      obtain ⟨count, occurrence, listed, rejected⟩ :=
        existsCause.imp (fun _ member => List.mem_filterMap.mp member)
      cases taskFound : cached.taskNode? occurrence with
      | none => simp [taskFound] at rejected
      | some taskNode =>
          have retained : taskNode.rejection = some count := by
            simpa [taskFound] using rejected
          have same := (State.taskNode?_some taskFound).2
          have taskFresh := fresh taskNode (List.mem_of_find?_eq_some taskFound) count retained
          obtain ⟨task, registered, identity, contributes⟩ :=
            cachedSound node (List.mem_of_find?_eq_some found) occurrence listed
          have direct : GroupRecordInvalidated work [task.occurrence] node.group.node.ref := by
            obtain ⟨⟨_, payload, producer, _, known⟩, _⟩ := cachedMatching task registered
            exact .task ⟨producer, payload, known⟩ contributes List.mem_cons_self
          exact markers.removeGroup (structural.cacheTaskFailures available)
            (accounted.cacheTaskFailures available) generated
            (links.cacheTaskFailures available) (records.cacheTaskFailures available)
            canonical registered (cachedMatching task registered)
            (by rwa [identity, ← same]) node.group.node.ref direct

/-- Released startup threads fresh cached causes and cancellation-aware evidence.
The invariant uses actual cancellation fields and success-only consumption; queued notices
are retained by the implementation's ordinary startup fold.
-/
theorem State.UncancelledRetiredMarkers.startNewWork {queue : State}
    {work parents settled}
    (prior : queue.UncancelledRetiredMarkers work)
    (structural : queue.UncancelledRetiredAncestors work)
    (accounted : queue.UncancelledTaskAccounting settled) (generated : ExecutedWork work)
    (links : queue.ChildLinksCanonical parents) (records : queue.GroupNodesMatchWork work)
    (sound : queue.GroupMembershipSound) (matching : queue.RegisteredTasksMatch work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (rejections : queue.TaskRejectionsSatisfy (fun occurrence _ => occurrence ∉ settled))
    (released : NewWork) (available : List (Occurrence × Nat))
    (licensed
      : ∀ occurrence errors, (occurrence, errors) ∈ available → occurrence ∉ settled)
    : (queue.startNewWork released available).1.UncancelledRetiredMarkers work := by
  let invariant (current : State) := current.UncancelledRetiredMarkers work
    ∧ current.UncancelledRetiredAncestors work ∧ current.UncancelledTaskAccounting settled
    ∧ current.ChildLinksCanonical parents ∧ current.GroupNodesMatchWork work
    ∧ current.GroupMembershipSound ∧ current.RegisteredTasksMatch work
    ∧ current.TaskRejectionsSatisfy (fun occurrence _ => occurrence ∉ settled)
  have loop (refs : NodeRefs) (acc : State × List GroupFailureEvent)
      (frame : invariant acc.1)
      : invariant (refs.foldl (fun (current, failures) ref =>
          let (next, queued) := current.startGroup ref available
          (next, failures ++ queued)) acc).1 := by
    induction refs generalizing acc with
    | nil => exact frame
    | cons ref rest ih =>
        exact ih _ ⟨frame.1.startGroup frame.2.1 frame.2.2.1 generated
            frame.2.2.2.1 frame.2.2.2.2.1 frame.2.2.2.2.2.1 frame.2.2.2.2.2.2.1
            canonical frame.2.2.2.2.2.2.2 ref available licensed,
          frame.2.1.startGroup ref available, frame.2.2.1.startGroup ref available,
          fun node member => frame.2.2.2.1 node
            ((acc.1.startGroup_groupNodes_sublist ref available).subset member),
          fun node member => frame.2.2.2.2.1 node
            ((acc.1.startGroup_groupNodes_sublist ref available).subset member),
          frame.2.2.2.2.2.1.startGroup ref available,
          frame.2.2.2.2.2.2.1.startGroup ref available,
          frame.2.2.2.2.2.2.2.startGroup ref available licensed⟩
  have grouped := loop (released.newGroups.map Execution.DeliveryNode.ref)
    ({ queue with rootGroups := queue.rootGroups ++
      released.newGroups.map Execution.DeliveryNode.ref }, [])
    ⟨prior, structural, accounted, links, records, sound, matching, rejections⟩
  have streams (refs : NodeRefs) (current : State)
      (frame : current.UncancelledRetiredMarkers work)
      : (refs.foldl State.startStream current).UncancelledRetiredMarkers work := by
    induction refs generalizing current with
    | nil => exact frame
    | cons ref rest ih =>
        apply ih
        unfold State.startStream
        split <;> exact frame
  exact streams _ _ grouped.1

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
