import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupRemoval
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.FailureProjection

/-! Active-root health through task-failure settlement. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Root presence rules out an active root whose live group lookup is absent. -/
private theorem State.RootGroupsPresent.rootAbsentIfMissing
    {queue : State} (present : queue.RootGroupsPresent)
    (ref : NodeRef) (missing : queue.groupNode? ref = none)
    : ref ∉ queue.rootGroups := by
  intro rootMember
  obtain ⟨node, nodeMember, same⟩ :=
    List.mem_map.mp (present ref rootMember)
  have noMatch := (List.find?_eq_none.mp missing) node nodeMember
  exact noMatch (beq_iff_eq.mpr same)

/-- An accepted failure removes every contributor from the active root set.
Witness: the owner fold closes announced groups and never activates cached latent ones.
An ignored late settlement adds no failure and need not remove its retained owners. -/
private theorem State.taskFailure_ownerRootsAbsent
    {queue : State} (present : queue.RootGroupsPresent)
    (occurrence : Occurrence) (errors : Nat)
    (taskNode : TaskNode) (found : queue.taskNode? occurrence = some taskNode)
    (accepted : queue.taskHasHealthyOwner taskNode.task = true)
    : ∀ ref ∈ taskNode.task.groups.map Execution.DeliveryNode.ref,
        ref ∉ (queue.taskFailure occurrence errors).1.rootGroups := by
  let step (acc : State × List WorkQueueEvent)
      (group : Execution.DeliveryNode) : State × List WorkQueueEvent :=
    let (current, events) := acc
    match current.groupNode? group.ref with
    | none => (current, events)
    | some node =>
        if current.rootGroups.contains group.ref then
          let (next, failure) := current.finishGroupFailure node errors
          (next, events ++ [failure])
        else (current.putGroupNode
          { node with
            pending := node.pending - 1
            failure := some (node.failure.getD 0 + errors) }, events)
  have stepFacts (acc : State × List WorkQueueEvent)
      (group : Execution.DeliveryNode)
      (currentPresent : acc.1.RootGroupsPresent)
      : (step acc group).1.RootGroupsPresent
        ∧ (step acc group).1.rootGroups.Subset acc.1.rootGroups
        ∧ group.ref ∉ (step acc group).1.rootGroups := by
    obtain ⟨current, events⟩ := acc
    cases nodeFound : current.groupNode? group.ref with
    | none =>
        have absent := currentPresent.rootAbsentIfMissing group.ref nodeFound
        simpa [step, nodeFound]
          using (show current.RootGroupsPresent
                      ∧ current.rootGroups.Subset current.rootGroups
                      ∧ group.ref ∉ current.rootGroups from ⟨
                  currentPresent,
                  List.Subset.refl _,
                  absent
                ⟩)
    | some node =>
        have nodeRef := current.groupNode?_ref nodeFound
        have removedPresent := currentPresent.removeGroup group.ref
        have removedSubset := current.removeGroup_rootsSubset group.ref
        have removedAbsent := current.removeGroup_rootAbsent group.ref node nodeFound
        by_cases active : group.ref ∈ current.rootGroups
        · simpa [step, nodeFound, active, State.finishGroupFailure, nodeRef]
            using (show (current.removeGroup group.ref).RootGroupsPresent
                        ∧ (current.removeGroup group.ref).rootGroups.Subset
                            current.rootGroups
                        ∧ group.ref ∉ (current.removeGroup group.ref).rootGroups from ⟨
                    removedPresent,
                    removedSubset,
                    removedAbsent
                  ⟩)
        · have inactive : current.rootGroups.contains group.ref = false := by simpa using active
          simp only [step, nodeFound, inactive, Bool.false_eq_true, ite_false]
          refine ⟨?_, List.Subset.refl _, active⟩
          intro ref member
          change ref ∈ ((current.putGroupNode _).groupNodes.map
            (fun node => node.group.node.ref))
          rw [State.putGroupNode_refs]
          exact currentPresent ref member
  have stepSubset (acc : State × List WorkQueueEvent)
      (group : Execution.DeliveryNode)
      : (step acc group).1.rootGroups.Subset acc.1.rootGroups := by
    obtain ⟨current, events⟩ := acc
    cases nodeFound : current.groupNode? group.ref with
    | none =>
        simp only [step, nodeFound]
        change current.rootGroups.Subset current.rootGroups
        exact List.Subset.refl _
    | some node =>
        have nodeRef := current.groupNode?_ref nodeFound
        by_cases active : group.ref ∈ current.rootGroups
        · simpa [step, nodeFound, active, State.finishGroupFailure, nodeRef]
            using current.removeGroup_rootsSubset group.ref
        · have inactive : current.rootGroups.contains group.ref = false := by simpa using active
          simp only [step, nodeFound, inactive, Bool.false_eq_true, ite_false]
          exact List.Subset.refl _
  have foldSubset (more : List Execution.DeliveryNode)
      (acc : State × List WorkQueueEvent)
      : (more.foldl step acc).1.rootGroups.Subset acc.1.rootGroups := by
    induction more generalizing acc with
    | nil => exact List.Subset.refl _
    | cons group rest ih =>
        exact (ih (step acc group)).trans (stepSubset acc group)
  have foldAbsent (more : List Execution.DeliveryNode)
      (acc : State × List WorkQueueEvent)
      (currentPresent : acc.1.RootGroupsPresent)
      : ∀ ref ∈ more.map Execution.DeliveryNode.ref,
          ref ∉ (more.foldl step acc).1.rootGroups := by
    induction more generalizing acc with
    | nil => intro ref member; cases member
    | cons group rest ih =>
        intro ref member
        obtain ⟨nextPresent, nextSubset, headAbsent⟩ :=
          stepFacts acc group currentPresent
        simp only [List.map_cons, List.mem_cons] at member
        rcases member with same | tail
        · subst ref
          intro rootMember
          exact headAbsent (foldSubset rest (step acc group) rootMember)
        · exact ih (step acc group) nextPresent ref tail
  let current := queue.removeTask occurrence
  have currentPresent : current.RootGroupsPresent := by
    intro ref member
    simpa [current, State.removeTask, List.map_map] using present ref member
  unfold State.taskFailure
  simp only [found, accepted, Bool.not_true, Bool.false_eq_true, ite_false]
  exact foldAbsent taskNode.task.groups (current, []) currentPresent

/-- A direct owner of an accepted failed task is absent from the resulting roots.
Witness: exact task provenance identifies the stored and structural contributor lists,
then the accepted-failure owner fold removes their active refs. -/
private theorem State.taskFailure_directOwnerAbsent
    {queue : State} {work : Execution.Work}
    (present : queue.RootGroupsPresent)
    (registered : queue.StartedTasksRegistered)
    (matching : queue.RegisteredTasksMatch work)
    (occurrence : Occurrence) (errors : Nat)
    (taskNode : TaskNode) (found : queue.taskNode? occurrence = some taskNode)
    (accepted : queue.taskHasHealthyOwner taskNode.task = true)
    {owners : NodeRefs} (known : TaskHasOwners work occurrence owners)
    {ref : NodeRef} (owner : ref ∈ owners)
    : ref ∉ (queue.taskFailure occurrence errors).1.rootGroups := by
  obtain ⟨producer, payload, taskAt⟩ := known
  have taskMember : taskNode.task ∈ queue.tasks :=
    registered taskNode (List.mem_of_find?_eq_some found)
  obtain ⟨⟨address, result, taskProducer, occurrenceEq, knownTask⟩, _⟩ :=
    matching taskNode.task taskMember
  have foundOccurrence : taskNode.task.occurrence = occurrence := by
    have selected := List.find?_some
      (p := fun candidate : TaskNode => candidate.task.occurrence == occurrence)
      (by simpa [State.taskNode?] using found)
    exact (occurrence_beq_iff_eq _ _).mp selected
  rw [foundOccurrence] at knownTask
  have ownerEq := (TaskAt.unique taskAt knownTask).1
  rw [ownerEq] at owner
  exact queue.taskFailure_ownerRootsAbsent present occurrence errors
    taskNode found accepted ref owner

/-- A defer group remains uninvalidated after an accepted failure when its ancestors do.
Witness: a direct failure either predates this step, contradicting old root health,
or is the just-settled task, whose contributor ref was removed. Cleanup invalidation
does not inspect the group's producer.
-/
theorem State.taskFailure_groupHealthy {queue : State} {work : Execution.Work}
    {failed : List Occurrence} (generated : ExecutedWork work)
    (healthy : queue.RootGroupsHealthy work failed) (present : queue.RootGroupsPresent)
    (registered : queue.StartedTasksRegistered)
    (matching : queue.RegisteredTasksMatch work) (occurrence : Occurrence) (errors : Nat)
    (taskNode : TaskNode) (found : queue.taskNode? occurrence = some taskNode)
    (accepted : queue.taskHasHealthyOwner taskNode.task = true)
    (node : Execution.DeliveryNode) (dependencies : NodeRefs)
    (producer : Option Occurrence)
    (active : node.ref ∈ (queue.taskFailure occurrence errors).1.rootGroups)
    (known : NodeAt work node .group dependencies producer)
    (ancestorsHealthy
      : ∀ dependency ∈ dependencies,
          ¬GroupInvalidated work (occurrence :: failed) dependency)
    : ¬GroupInvalidated work (occurrence :: failed) node.ref := by
  intro failure
  have oldActive : node.ref ∈ queue.rootGroups :=
    queue.taskFailure_rootsSubset occurrence errors active
  rcases generated.groupInvalidated_causes known failure with
    ⟨failedTask, owners, taskKnown, owner, failedMember⟩
    | ⟨dependency, member, ancestorFailure⟩
  · rcases List.mem_cons.mp failedMember with same | earlier
    · subst failedTask
      exact (queue.taskFailure_directOwnerAbsent present registered matching
        occurrence errors taskNode found accepted taskKnown owner) active
    · exact (healthy node.ref oldActive)
        (GroupInvalidated.task taskKnown owner earlier)
  · exact ancestorsHealthy dependency member ancestorFailure

/-- After an accepted failure a healthy surviving root becomes invalidated exactly when
the failed task owns one of its defer ancestors. Direct ownership cannot be the cause:
the failure handler has already removed every direct owner from the root set.
Witness: the flat new-failure characterization and direct-owner removal.
-/
theorem State.taskFailure_survivorInvalidated_iff
    {queue : State} {work : Execution.Work} {failed : List Occurrence}
    (generated : ExecutedWork work)
    (healthy : queue.RootGroupsHealthy work failed)
    (present : queue.RootGroupsPresent)
    (registered : queue.StartedTasksRegistered)
    (matching : queue.RegisteredTasksMatch work)
    (occurrence : Occurrence) (errors : Nat)
    (taskNode : TaskNode) (found : queue.taskNode? occurrence = some taskNode)
    (accepted : queue.taskHasHealthyOwner taskNode.task = true)
    {owners} (task : TaskHasOwners work occurrence owners)
    {node dependencies producer}
    (active : node.ref ∈ (queue.taskFailure occurrence errors).1.rootGroups)
    (known : NodeAt work node .group dependencies producer)
    : GroupInvalidated work (occurrence :: failed) node.ref
      ↔ ∃ owner ∈ owners, owner ∈ dependencies := by
  have oldHealthy := healthy node.ref
    (queue.taskFailure_rootsSubset occurrence errors active)
  rw [generated.groupInvalidated_cons_iff known oldHealthy task]
  constructor
  · rintro ⟨owner, contributes, member⟩
    rcases List.mem_cons.mp member with direct | ancestor
    · subst owner
      exact False.elim ((queue.taskFailure_directOwnerAbsent present registered matching
        occurrence errors taskNode found accepted task contributes) active)
    · exact ⟨owner, contributes, ancestor⟩
  · rintro ⟨owner, contributes, ancestor⟩
    exact ⟨owner, contributes, List.mem_cons.mpr (.inr ancestor)⟩

/-- Accepted failures preserve healthy roots while the active frontier remains a subset
of its initial notices. No extra ancestor-health premise is needed: initialization
already rules out contributing tasks for every dependency of those groups.
Witness: initial dependency protection plus per-group failure preservation.
-/
theorem State.RootGroupsHealthy.taskFailure_initialFrontier
    {queue : State} {work : Execution.Work} {failed : List Occurrence} {groups streams}
    (healthy : queue.RootGroupsHealthy work failed)
    (generated : ExecutedWork work)
    (initialized : Initializes work groups streams)
    (frontier : queue.rootGroups.Subset (groups.map Execution.DeliveryNode.ref))
    (present : queue.RootGroupsPresent)
    (registered : queue.StartedTasksRegistered)
    (matching : queue.RegisteredTasksMatch work)
    (occurrence : Occurrence) (errors : Nat)
    (taskNode : TaskNode) (found : queue.taskNode? occurrence = some taskNode)
    (accepted : queue.taskHasHealthyOwner taskNode.task = true)
    : (queue.taskFailure occurrence errors).1.RootGroupsHealthy
        work (occurrence :: failed) := by
  intro ref active
  have oldActive := queue.taskFailure_rootsSubset occurrence errors active
  obtain ⟨node, member, same⟩ := List.mem_map.mp (frontier oldActive)
  obtain ⟨dependencies, producer, known, protection⟩ :=
    Initializes.groupDependencies_uninvalidated initialized member
  rw [← same] at active ⊢
  exact queue.taskFailure_groupHealthy generated healthy present registered matching
    occurrence errors taskNode found accepted node dependencies producer active known
    (fun ancestor member => protection (occurrence :: failed) ancestor member)

/-- Every failure input preserves initial-frontier health under the accepted inventory.
Witness: accepted tasks use owner removal; missing or fully invalidated tasks add no
failure token and leave group roots unchanged. No acceptance premise is imposed. -/
theorem State.RootGroupsHealthy.taskFailure_initialFrontier_contributions
    {queue : State} {work : Execution.Work} {failed : List Occurrence} {groups streams}
    (healthy : queue.RootGroupsHealthy work failed)
    (generated : ExecutedWork work)
    (initialized : Initializes work groups streams)
    (frontier : queue.rootGroups.Subset (groups.map Execution.DeliveryNode.ref))
    (present : queue.RootGroupsPresent)
    (registered : queue.StartedTasksRegistered)
    (matching : queue.RegisteredTasksMatch work)
    (occurrence : Occurrence) (errors : Nat)
    : (queue.taskFailure occurrence errors).1.RootGroupsHealthy work
        (queue.objectFailureContribution (.taskFailure occurrence errors) ++ failed) := by
  cases found : queue.taskNode? occurrence with
  | none =>
      simpa [State.taskFailure, State.objectFailureContribution, found] using healthy
  | some node =>
      cases accepted : queue.taskHasHealthyOwner node.task with
      | false =>
          simpa [State.taskFailure, State.objectFailureContribution, found, accepted,
            State.RootGroupsHealthy, State.removeTask] using healthy
      | true =>
          simpa [State.objectFailureContribution, found, accepted]
            using healthy.taskFailure_initialFrontier generated initialized frontier
              present registered matching occurrence errors node found accepted

/-- An accepted failure preserves healthy roots with healthy defer ancestors.
Witness: contributor-ref support supplies a real structural node for each active root;
registration records alone are insufficient because ancestors may be taskless.
The dependency condition is proof-side evidence, not a public conformance premise.
-/
theorem State.RootGroupsHealthy.taskFailure_of_healthyDependencies
    {queue : State} {work : Execution.Work} {failed : List Occurrence}
    (healthy : queue.RootGroupsHealthy work failed)
    (generated : ExecutedWork work)
    (present : queue.RootGroupsPresent)
    (registered : queue.StartedTasksRegistered)
    (matching : queue.RegisteredTasksMatch work)
    (rootsKnown
      : ∀ ref ∈ queue.rootGroups,
          ∃ dependencies, NodeHasDependencies work ref .group dependencies)
    (occurrence : Occurrence) (errors : Nat)
    (taskNode : TaskNode) (found : queue.taskNode? occurrence = some taskNode)
    (accepted : queue.taskHasHealthyOwner taskNode.task = true)
    (ancestorsHealthy
      : ∀ node dependencies producer,
          node.ref ∈ (queue.taskFailure occurrence errors).1.rootGroups
          → NodeAt work node .group dependencies producer
          → ∀ dependency ∈ dependencies,
              ¬GroupInvalidated work (occurrence :: failed) dependency)
    : (queue.taskFailure occurrence errors).1.RootGroupsHealthy
        work (occurrence :: failed) := by
  intro ref active
  have oldActive := queue.taskFailure_rootsSubset occurrence errors active
  obtain ⟨dependencies, node, producer, known, same⟩ := rootsKnown ref oldActive
  rw [← same] at active ⊢
  exact queue.taskFailure_groupHealthy generated healthy present registered matching
    occurrence errors taskNode found accepted node dependencies producer active known
    (ancestorsHealthy node dependencies producer active known)

/-- An accepted failure cannot leave a failed root defer group active.
Witness: ancestor-free groups discharge the remaining dependency condition directly.
-/
private theorem State.taskFailure_rootGroupHealthy
    {queue : State} {work : Execution.Work} {failed : List Occurrence}
    (generated : ExecutedWork work)
    (healthy : queue.RootGroupsHealthy work failed)
    (present : queue.RootGroupsPresent)
    (registered : queue.StartedTasksRegistered)
    (matching : queue.RegisteredTasksMatch work)
    (occurrence : Occurrence) (errors : Nat)
    (taskNode : TaskNode) (found : queue.taskNode? occurrence = some taskNode)
    (accepted : queue.taskHasHealthyOwner taskNode.task = true)
    : ∀ node : Execution.DeliveryNode,
        node.ref ∈ (queue.taskFailure occurrence errors).1.rootGroups
        → NodeAt work node .group [] none
        → ¬GroupInvalidated work (occurrence :: failed) node.ref := by
  intro node active rootKnown
  exact queue.taskFailure_groupHealthy generated healthy present
    registered matching occurrence errors taskNode found accepted node [] none active
    rootKnown (by intro dependency member; cases member)

/-- Accepted failure preserves health when all active groups have no ancestors.
Witness: specialize the per-root result to unproduced root groups. -/
private theorem State.RootGroupsHealthy.taskFailure_rootOnly
    {queue : State} {work : Execution.Work} {failed : List Occurrence}
    (generated : ExecutedWork work)
    (healthy : queue.RootGroupsHealthy work failed)
    (present : queue.RootGroupsPresent)
    (registered : queue.StartedTasksRegistered)
    (matching : queue.RegisteredTasksMatch work)
    (rootOnly
      : ∀ ref ∈ queue.rootGroups,
          ∃ node : Execution.DeliveryNode,
            node.ref = ref ∧ NodeAt work node .group [] none)
    (occurrence : Occurrence) (errors : Nat)
    (taskNode : TaskNode) (found : queue.taskNode? occurrence = some taskNode)
    (accepted : queue.taskHasHealthyOwner taskNode.task = true)
    : (queue.taskFailure occurrence errors).1.RootGroupsHealthy
        work (occurrence :: failed) := by
  intro ref active
  have oldActive : ref ∈ queue.rootGroups :=
    queue.taskFailure_rootsSubset occurrence errors active
  obtain ⟨node, refEq, known⟩ := rootOnly ref oldActive
  rw [← refEq] at active ⊢
  exact queue.taskFailure_rootGroupHealthy generated healthy present
    registered matching occurrence errors taskNode found accepted node active known

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
