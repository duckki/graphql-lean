import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupRemoval
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.FailureProjection

/-! Active-root health through task-failure settlement. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Root presence rules out an active root whose live group lookup is absent. -/
private theorem State.RootGroupsPresent.rootAbsentIfMissing
    {queue : State} (present : queue.RootGroupsPresent)
    (key : Nat) (missing : queue.groupNode? key = none)
    : key ∉ queue.rootGroups := by
  intro rootMember
  obtain ⟨node, nodeMember, same⟩ :=
    List.mem_map.mp (present key rootMember)
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
    : ∀ key ∈ taskNode.task.groups.map Execution.DeliveryNode.key,
        key ∉ (queue.taskFailure occurrence errors).1.rootGroups := by
  let step (acc : State × List WorkQueueEvent)
      (group : Execution.DeliveryNode) : State × List WorkQueueEvent :=
    let (current, events) := acc
    match current.groupNode? group.key with
    | none => (current, events)
    | some node =>
        if current.rootGroups.contains group.key then
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
        ∧ group.key ∉ (step acc group).1.rootGroups := by
    obtain ⟨current, events⟩ := acc
    cases nodeFound : current.groupNode? group.key with
    | none =>
        have absent := currentPresent.rootAbsentIfMissing group.key nodeFound
        simpa [step, nodeFound]
          using (show current.RootGroupsPresent
                      ∧ current.rootGroups.Subset current.rootGroups
                      ∧ group.key ∉ current.rootGroups from ⟨
                  currentPresent,
                  List.Subset.refl _,
                  absent
                ⟩)
    | some node =>
        have nodeKey := current.groupNode?_key nodeFound
        have removedPresent := currentPresent.removeGroup group.key
        have removedSubset := current.removeGroup_rootsSubset group.key
        have removedAbsent := current.removeGroup_rootAbsent group.key node nodeFound
        by_cases active : group.key ∈ current.rootGroups
        · simpa [step, nodeFound, active, State.finishGroupFailure, nodeKey]
            using (show (current.removeGroup group.key).RootGroupsPresent
                        ∧ (current.removeGroup group.key).rootGroups.Subset
                            current.rootGroups
                        ∧ group.key ∉ (current.removeGroup group.key).rootGroups from ⟨
                    removedPresent,
                    removedSubset,
                    removedAbsent
                  ⟩)
        · have inactive : current.rootGroups.contains group.key = false := by simpa using active
          simp only [step, nodeFound, inactive, Bool.false_eq_true, ite_false]
          refine ⟨?_, List.Subset.refl _, active⟩
          intro key member
          change key ∈ ((current.putGroupNode _).groupNodes.map
            (fun node => node.group.node.key))
          rw [State.putGroupNode_keys]
          exact currentPresent key member
  have stepSubset (acc : State × List WorkQueueEvent)
      (group : Execution.DeliveryNode)
      : (step acc group).1.rootGroups.Subset acc.1.rootGroups := by
    obtain ⟨current, events⟩ := acc
    cases nodeFound : current.groupNode? group.key with
    | none =>
        simp only [step, nodeFound]
        change current.rootGroups.Subset current.rootGroups
        exact List.Subset.refl _
    | some node =>
        have nodeKey := current.groupNode?_key nodeFound
        by_cases active : group.key ∈ current.rootGroups
        · simpa [step, nodeFound, active, State.finishGroupFailure, nodeKey]
            using current.removeGroup_rootsSubset group.key
        · have inactive : current.rootGroups.contains group.key = false := by simpa using active
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
      : ∀ key ∈ more.map Execution.DeliveryNode.key,
          key ∉ (more.foldl step acc).1.rootGroups := by
    induction more generalizing acc with
    | nil => intro key member; cases member
    | cons group rest ih =>
        intro key member
        obtain ⟨nextPresent, nextSubset, headAbsent⟩ :=
          stepFacts acc group currentPresent
        simp only [List.map_cons, List.mem_cons] at member
        rcases member with same | tail
        · subst key
          intro rootMember
          exact headAbsent (foldSubset rest (step acc group) rootMember)
        · exact ih (step acc group) nextPresent key tail
  let current := queue.removeTask occurrence
  have currentPresent : current.RootGroupsPresent := by
    intro key member
    simpa [current, State.removeTask, List.map_map] using present key member
  unfold State.taskFailure
  simp only [found, accepted, Bool.not_true, Bool.false_eq_true, ite_false]
  exact foldAbsent taskNode.task.groups (current, []) currentPresent

/-- A direct owner of an accepted failed task is absent from the resulting roots.
Witness: exact task provenance identifies the stored and structural contributor lists,
then the accepted-failure owner fold removes their active keys. -/
private theorem State.taskFailure_directOwnerAbsent
    {queue : State} {work : Execution.Work}
    (present : queue.RootGroupsPresent)
    (registered : queue.StartedTasksRegistered)
    (matching : queue.RegisteredTasksMatch work)
    (occurrence : Occurrence) (errors : Nat)
    (taskNode : TaskNode) (found : queue.taskNode? occurrence = some taskNode)
    (accepted : queue.taskHasHealthyOwner taskNode.task = true)
    {owners : Keys} (known : TaskHasOwners work occurrence owners)
    {key : Nat} (owner : key ∈ owners)
    : key ∉ (queue.taskFailure occurrence errors).1.rootGroups := by
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
    taskNode found accepted key owner

/-- A defer group remains uninvalidated after an accepted failure when its ancestors do.
Witness: a direct failure either predates this step, contradicting old root health,
or is the just-settled task, whose contributor key was removed. Cleanup invalidation
does not inspect the group's producer.
-/
theorem State.taskFailure_groupHealthy
    {queue : State} {work : Execution.Work} {failed : List Occurrence}
    (generated : ExecutedWork work)
    (healthy : queue.RootGroupsHealthy work failed)
    (present : queue.RootGroupsPresent)
    (registered : queue.StartedTasksRegistered)
    (matching : queue.RegisteredTasksMatch work)
    (occurrence : Occurrence) (errors : Nat)
    (taskNode : TaskNode) (found : queue.taskNode? occurrence = some taskNode)
    (accepted : queue.taskHasHealthyOwner taskNode.task = true)
    (node : Execution.DeliveryNode) (dependencies : Keys) (producer : Option Occurrence)
    (active : node.key ∈ (queue.taskFailure occurrence errors).1.rootGroups)
    (known : NodeAt work node .group dependencies producer)
    (ancestorsHealthy
      : ∀ dependency ∈ dependencies,
          ¬GroupInvalidated work (occurrence :: failed) dependency)
    : ¬GroupInvalidated work (occurrence :: failed) node.key := by
  intro failure
  have oldActive : node.key ∈ queue.rootGroups :=
    queue.taskFailure_rootsSubset occurrence errors active
  rcases generated.groupInvalidated_causes known failure with
    ⟨failedTask, owners, taskKnown, owner, failedMember⟩
    | ⟨dependency, member, ancestorFailure⟩
  · rcases List.mem_cons.mp failedMember with same | earlier
    · subst failedTask
      exact (queue.taskFailure_directOwnerAbsent present registered matching
        occurrence errors taskNode found accepted taskKnown owner) active
    · exact (healthy node.key oldActive)
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
    (active : node.key ∈ (queue.taskFailure occurrence errors).1.rootGroups)
    (known : NodeAt work node .group dependencies producer)
    : GroupInvalidated work (occurrence :: failed) node.key
      ↔ ∃ owner ∈ owners, owner ∈ dependencies := by
  have oldHealthy := healthy node.key
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
    (frontier : queue.rootGroups.Subset (groups.map Execution.DeliveryNode.key))
    (present : queue.RootGroupsPresent)
    (registered : queue.StartedTasksRegistered)
    (matching : queue.RegisteredTasksMatch work)
    (occurrence : Occurrence) (errors : Nat)
    (taskNode : TaskNode) (found : queue.taskNode? occurrence = some taskNode)
    (accepted : queue.taskHasHealthyOwner taskNode.task = true)
    : (queue.taskFailure occurrence errors).1.RootGroupsHealthy
        work (occurrence :: failed) := by
  intro key active
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
    (frontier : queue.rootGroups.Subset (groups.map Execution.DeliveryNode.key))
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
Witness: contributor-key support supplies a real structural node for each active root;
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
      : ∀ key ∈ queue.rootGroups,
          ∃ dependencies, NodeHasDependencies work key .group dependencies)
    (occurrence : Occurrence) (errors : Nat)
    (taskNode : TaskNode) (found : queue.taskNode? occurrence = some taskNode)
    (accepted : queue.taskHasHealthyOwner taskNode.task = true)
    (ancestorsHealthy
      : ∀ node dependencies producer,
          node.key ∈ (queue.taskFailure occurrence errors).1.rootGroups
          → NodeAt work node .group dependencies producer
          → ∀ dependency ∈ dependencies,
              ¬GroupInvalidated work (occurrence :: failed) dependency)
    : (queue.taskFailure occurrence errors).1.RootGroupsHealthy
        work (occurrence :: failed) := by
  intro key active
  have oldActive := queue.taskFailure_rootsSubset occurrence errors active
  obtain ⟨dependencies, node, producer, known, same⟩ := rootsKnown key oldActive
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
        node.key ∈ (queue.taskFailure occurrence errors).1.rootGroups
        → NodeAt work node .group [] none
        → ¬GroupInvalidated work (occurrence :: failed) node.key := by
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
      : ∀ key ∈ queue.rootGroups,
          ∃ node : Execution.DeliveryNode,
            node.key = key ∧ NodeAt work node .group [] none)
    (occurrence : Occurrence) (errors : Nat)
    (taskNode : TaskNode) (found : queue.taskNode? occurrence = some taskNode)
    (accepted : queue.taskHasHealthyOwner taskNode.task = true)
    : (queue.taskFailure occurrence errors).1.RootGroupsHealthy
        work (occurrence :: failed) := by
  intro key active
  have oldActive : key ∈ queue.rootGroups :=
    queue.taskFailure_rootsSubset occurrence errors active
  obtain ⟨node, keyEq, known⟩ := rootOnly key oldActive
  rw [← keyEq] at active ⊢
  exact queue.taskFailure_rootGroupHealthy generated healthy present
    registered matching occurrence errors taskNode found accepted node active known

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
