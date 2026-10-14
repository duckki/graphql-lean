import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.RegistrationProjection

/-! The owner-loop's active projection agrees with the reference root test on live roots. -/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue

-----------------------------------------------------------------------------------------
-- Live-root eligibility is a derived reference invariant, not a host premise
-----------------------------------------------------------------------------------------

private theorem registerOwner_keys (task : ReferenceWorkQueue.Task)
    (queue : ReferenceWorkQueue.State) (group : Execution.DeliveryNode)
    : (registerOwner task queue group).groupNodes.map (fun node => node.group.node.ref)
      = queue.groupNodes.map (fun node => node.group.node.ref) := by
  unfold registerOwner
  split
  · rfl
  · split
    · rfl
    · exact ReferenceWorkQueue.State.putGroupNode_refs _ _

private theorem registerOwner_rootsPresent (task : ReferenceWorkQueue.Task)
    (queue : ReferenceWorkQueue.State) (present : queue.RootGroupsPresent)
    (group : Execution.DeliveryNode)
    : (registerOwner task queue group).RootGroupsPresent := by
  intro key member
  rw [registerOwner_rootGroups] at member
  rw [registerOwner_keys]
  exact present key member

private theorem missing_root_inactive (queue : ReferenceWorkQueue.State)
    (present : queue.RootGroupsPresent) (key : Nat) (absent : queue.groupNode? key = none)
    : queue.rootGroups.contains key = false := by
  cases test : queue.rootGroups.contains key with
  | false => rfl
  | true =>
      obtain ⟨node, member, same⟩ := List.mem_map.mp
        (present key (List.contains_iff_mem.mp test))
      have excluded := List.find?_eq_none.mp absent node member
      exact (excluded (beq_iff_eq.mpr same)).elim

private theorem classifyOwners_active (task : ReferenceWorkQueue.Task)
    (owners : List Execution.DeliveryNode) (acc : ReferenceWorkQueue.State × Bool × Bool)
    (present : acc.1.RootGroupsPresent)
    : (owners.foldl (classifyOwner task) acc).2.2
      = (acc.2.2 || owners.any (fun group => acc.1.rootGroups.contains group.ref)) := by
  induction owners generalizing acc with
  | nil => simp
  | cons group rest ih =>
      have nextPresent : (classifyOwner task acc group).1.RootGroupsPresent := by
        rw [classifyOwner_core]
        exact registerOwner_rootsPresent task acc.1 present group
      have roots : (classifyOwner task acc group).1.rootGroups = acc.1.rootGroups := by
        rw [classifyOwner_core, registerOwner_rootGroups]
      have next : (classifyOwner task acc group).2.2
          = (acc.2.2 || acc.1.rootGroups.contains group.ref) := by
        cases found : acc.1.groupNode? group.ref with
        | none =>
            have inactive := missing_root_inactive acc.1 present group.ref found
            simp only [classifyOwner, found, inactive, Bool.or_false]
        | some node =>
            have unchanged := registerOwner_rootGroups task acc.1 group
            change (classifyOwner task acc group).2.2
              = (acc.2.2 || acc.1.rootGroups.contains group.ref)
            unfold classifyOwner
            simp only [found]
            simpa only [registerOwner, found] using congrArg (fun keys =>
              acc.2.2 || keys.contains group.ref) unchanged
      rw [List.foldl_cons, ih _ nextPresent, roots, next, List.any_cons, Bool.or_assoc]

/-- Active classification is exactly the reference root-owner test on present roots.
Witness: root presence rules out a missing-but-active owner, then the accumulated activity
flag is the Boolean any-test. Failed live roots are intentionally not excluded.
-/
theorem State.addTask_active_iff (state : State) (task : ReferenceWorkQueue.Task)
    (present : state.queue.RootGroupsPresent)
    : (state.addTask task).2 = .active
      ↔ task.groups.any (fun group => state.queue.rootGroups.contains group.ref)
        = true := by
  let registered := { state.queue with tasks := state.queue.tasks ++ [task] }
  have activity := classifyOwners_active task task.groups (registered, false, false) present
  simp only [Bool.false_or] at activity
  change (if (task.groups.foldl (classifyOwner task) (registered, false, false)).2.2 then
      TaskRegistration.active
    else if (task.groups.foldl (classifyOwner task) (registered, false, false)).2.1 then
      TaskRegistration.registered else TaskRegistration.rejected) = .active ↔ _
  rw [activity]
  split
  · simp_all [registered]
  · split <;> simp_all [registered]

end GraphQL.IncrementalDelivery.AlternativeWorkQueue
