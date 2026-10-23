import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.FailureRemoval
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.TaskEligibility
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.MembershipSoundness

/-! Replaying a sound active rejection removes at least one live group. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Failure processing retains a subsequence of the original live group records.
Witness: every owner step either preserves the state or filters group records.
-/
theorem State.taskFailure_groupNodes_sublist (queue : State) (occurrence : Occurrence)
    (errors : Nat)
    : (queue.taskFailure occurrence errors).1.groupNodes.Sublist queue.groupNodes := by
  cases found : queue.taskNode? occurrence with
  | none => simp [State.taskFailure, found]
  | some task =>
      rw [queue.taskFailure_eq occurrence errors task found]
      apply failureGroupFold_preserves
        (fun next => next.groupNodes.Sublist queue.groupNodes)
        (fun _ _ prior => List.filter_sublist.trans prior)
      exact .refl _

/-- A surviving group that was active remains active throughout a failure handler.
Witness: group and root removal use the same collected ref filter.
-/
theorem State.taskFailure_activeSurvivor {queue : State} {occurrence errors ref}
    (active : ref ∈ queue.rootGroups)
    : ∀ node ∈ (queue.taskFailure occurrence errors).1.groupNodes,
        node.group.node.ref = ref
        → ref ∈ (queue.taskFailure occurrence errors).1.rootGroups := by
  let invariant (next : State) :=
    ∀ node ∈ next.groupNodes, node.group.node.ref = ref → ref ∈ next.rootGroups
  have initial : invariant queue := fun _ _ _ => active
  cases found : queue.taskNode? occurrence with
  | none => simpa [State.taskFailure, found] using initial
  | some task =>
      rw [queue.taskFailure_eq occurrence errors task found]
      apply failureGroupFold_preserves invariant
        (fun current removed prior node member same => by
          have parts := List.mem_filter.mp member
          exact List.mem_filter.mpr ⟨prior node parts.1 same, same ▸ parts.2⟩)
      exact initial

/-- A live surviving contributor is dormant after its task rejection is processed.
Witness: visit every owner; a live active owner is removed, and later steps only filter
records and roots. Stale active refs with no live record impose no requirement.
-/
theorem State.taskFailure_ownerLiveRootsAbsent {queue : State} {occurrence errors task}
    (found : queue.taskNode? occurrence = some task)
    : ∀ ref ∈ task.task.groups.map Execution.DeliveryNode.ref,
      ∀ node ∈ (queue.taskFailure occurrence errors).1.groupNodes,
        node.group.node.ref = ref
        → ref ∉ (queue.taskFailure occurrence errors).1.rootGroups := by
  let property (ref : NodeRef) (current : State) :=
    ∀ node ∈ current.groupNodes, node.group.node.ref = ref → ref ∉ current.rootGroups
  have remove (ref : NodeRef) (current : State) (removed : NodeRef)
      (prior : property ref current) : property ref (current.removeGroup removed) := by
    intro node member same active
    exact prior node (List.mem_filter.mp member).1 same
      (current.removeGroup_rootsSubset removed active)
  have keep (ref : NodeRef) (groups : List Execution.DeliveryNode)
      (acc : State × List Execution.WorkQueueEvent) (prior : property ref acc.1)
      : property ref (groups.foldl (failureGroupStep errors) acc).1 :=
    failureGroupFold_preserves (property ref) (remove ref) errors groups acc prior
  have loop (groups : List Execution.DeliveryNode) (acc : State × List Execution.WorkQueueEvent)
      : ∀ ref ∈ groups.map Execution.DeliveryNode.ref,
          property ref (groups.foldl (failureGroupStep errors) acc).1 := by
    induction groups generalizing acc with
    | nil => simp
    | cons group rest ih =>
        intro ref included
        rcases List.mem_cons.mp included with same | tail
        · subst ref
          apply keep group.ref rest
          obtain ⟨current, events⟩ := acc
          dsimp only [failureGroupStep]
          split
          · rename_i absent
            intro node member equal
            have impossible := List.find?_eq_none.mp absent node member
            exact False.elim (impossible (beq_iff_eq.mpr equal))
          · rename_i node found
            split
            · intro other member equal
              have absent := current.removeGroup_ownGroupAbsent node.group.node.ref
              have impossible := List.find?_eq_none.mp absent other member
              exact False.elim (impossible
                (beq_iff_eq.mpr (equal.trans (current.groupNode?_ref found).symm)))
            · rename_i dormant
              intro _ _ _
              simpa using dormant
        · exact ih _ ref tail
  rw [queue.taskFailure_eq occurrence errors task found]
  exact loop task.task.groups _

/-- Replaying a rejection selected from a sound active group strictly decreases its live
node count. Witness: exact registered ownership makes the selected group an owner; the
failure fold removes that owner and only filters the other live records.
-/
theorem State.taskFailure_rejected_length_lt {queue : State} {work : Execution.Work}
    (sound : queue.GroupMembershipSound) (registered : queue.StartedTasksRegistered)
    (matching : queue.RegisteredTasksMatch work) {group : GroupNode}
    (member : group ∈ queue.groupNodes) (active : group.group.node.ref ∈ queue.rootGroups)
    {occurrence errors} (selected : queue.rejectedTask? group = some (occurrence, errors))
    : (queue.taskFailure occurrence errors).1.groupNodes.length
      < queue.groupNodes.length := by
  obtain ⟨listed, task, found, _⟩ := State.rejectedTask?_sound selected
  have same : task.task.occurrence = occurrence :=
    (occurrence_beq_iff_eq _ _).mp
      (List.find?_some (p := fun candidate : TaskNode => candidate.task.occurrence == occurrence)
        found)
  have owner := sound.startedOwner registered matching (List.mem_of_find?_eq_some found)
    member (same.symm ▸ listed)
  have absent := queue.taskFailure_ownerLiveRootsAbsent (errors := errors) found group.group.node.ref owner
  have sublist := queue.taskFailure_groupNodes_sublist occurrence errors
  have different : (queue.taskFailure occurrence errors).1.groupNodes ≠ queue.groupNodes := by
    intro equal
    have retained : group ∈ (queue.taskFailure occurrence errors).1.groupNodes := equal ▸ member
    exact absent group retained rfl (queue.taskFailure_activeSurvivor active group retained rfl)
  have bound := sublist.length_le
  have strict : (queue.taskFailure occurrence errors).1.groupNodes.length
      ≠ queue.groupNodes.length := fun equal => different (sublist.eq_of_length equal)
  omega

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
