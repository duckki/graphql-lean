import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.WorkDeclarations
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.OwnerAccounting

/-! Fresh integration candidates and their installed task memberships. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- New root candidates come only from parentless group registrations
-----------------------------------------------------------------------------------------

/-- Every new root is a parentless candidate that was absent at registration entry.
Witness: follow recursive parent visits and preserve the entry registry and live refs
through each installation. The resulting frontier follows installation order.
-/
theorem State.addGroups_newGroup_candidate (queue : State) (groups : List Group)
    {node : Execution.DeliveryNode} (member : node ∈ (queue.addGroups groups).2)
    : ∃ group ∈ groups,
        group.node = node
        ∧ group.parent = none
        ∧ node.ref ∉ queue.registeredGroups
        ∧ queue.groupNode? node.ref = none := by
  let candidate (node : Execution.DeliveryNode) := ∃ group ∈ groups,
    group.node = node ∧ group.parent = none ∧ node.ref ∉ queue.registeredGroups
      ∧ queue.groupNode? node.ref = none
  let retained (current : State) := queue.registeredGroups ⊆ current.registeredGroups
    ∧ queue.groupNodes.map (fun node => node.group.node.ref)
      ⊆ current.groupNodes.map (fun node => node.group.node.ref)
  have install (current : State) (group : Group) (_member : group ∈ groups)
      (prior : retained current) : retained (current.addGroup group) :=
    ⟨prior.1.trans (current.addGroup_registeredGroups_subset_old group),
      prior.2.trans (current.addGroup_refs_subset group)⟩
  have visit (fuel : Nat) (acc : State × List Execution.DeliveryNode × NodeRefs)
      (group : Group) (included : group ∈ groups) (prior : retained acc.1)
      (roots : ∀ node ∈ acc.2.1, candidate node)
      : ∀ node ∈ (State.addGroups.go groups fuel acc group).2.1, candidate node := by
    induction fuel generalizing acc group with
    | zero => exact roots
    | succ fuel ih =>
        obtain ⟨current, oldRoots, visited⟩ := acc
        simp only [State.addGroups.go]
        split
        · exact roots
        · split
          · exact roots
          · rename_i fresh
            have missing : group.node.ref ∉ current.registeredGroups
                ∧ current.groupNode? group.node.ref = none := by simpa using fresh
            have rootCandidate (parentless : group.parent = none) : candidate group.node := by
              refine ⟨group, included, rfl, parentless,
                fun registered => missing.1 (prior.1 registered), ?_⟩
              cases found : queue.groupNode? group.node.ref with
              | none => rfl
              | some live =>
                  have member := prior.2 (List.mem_map.mpr
                    ⟨live, List.mem_of_find?_eq_some found, State.groupNode?_ref found⟩)
                  obtain ⟨node, nodeMember, same⟩ := List.mem_map.mp member
                  exact False.elim (List.find?_eq_none.mp missing.2 node nodeMember
                    (beq_iff_eq.mpr same))
            split
            · intro node member
              split at member
              · rcases List.mem_append.mp member with old | new
                · exact roots node old
                · have equal := List.mem_singleton.mp new
                  exact equal ▸ rootCandidate (by simpa using ‹group.parent.isNone = true›)
              · exact roots node member
            · rename_i parent found
              obtain ⟨ref, parentEq, selected⟩ := Option.bind_eq_some_iff.mp found
              have parentRoots := ih (current, oldRoots, visited ++ [group.node.ref]) parent (List.mem_of_find?_eq_some selected) prior roots
              intro node member
              split at member
              · have parentless : group.parent = none := by
                  simpa using ‹group.parent.isNone = true›
                simp [parentless] at parentEq
              · exact parentRoots node member
  have fold (more : List Group) (included : more ⊆ groups)
      (acc : State × List Execution.DeliveryNode × NodeRefs) (prior : retained acc.1)
      (roots : ∀ node ∈ acc.2.1, candidate node)
      : ∀ node ∈ (more.foldl
          (fun acc group => State.addGroups.go groups (groups.length + 1) acc group) acc).2.1,
          candidate node := by
    induction more generalizing acc with
    | nil => exact roots
    | cons group rest ih =>
        exact ih (fun _ member => included (List.mem_cons_of_mem _ member)) _
          (State.addGroups.go_preserves retained groups install _ acc group
            (included List.mem_cons_self) prior)
          (visit _ acc group (included List.mem_cons_self) prior roots)
  exact fold groups (List.Subset.refl _) (queue, [], [])
    ⟨List.Subset.refl _, List.Subset.refl _⟩ (by simp) node member

/-- Task and stream registration do not change the group-root candidate list.
Witness: project the group component of the three-stage integration algorithm. -/
theorem State.maybeIntegrateWork_newGroups (queue : State) (work : Work)
    (parentTask : Option Occurrence := none)
    : (queue.maybeIntegrateWork work parentTask).2.newGroups
      = (queue.addGroups work.groups).2 := by
  rfl

-----------------------------------------------------------------------------------------
-- A newly integrated task protects its live contributors from pruning
-----------------------------------------------------------------------------------------

/-- Every newly integrated task is linked on all of its live contributor nodes.
Witness: install the link at its task-registration step and preserve it through later
task and stream registrations. No old-task accounting or availability premise is needed.
-/
theorem State.maybeIntegrateWork_newTask_linked
    {queue : State} (unique : queue.GroupRefsUnique) (work : Work)
    (parentTask : Option Occurrence := none)
    {task : Task} (member : task ∈ work.tasks)
    : (queue.maybeIntegrateWork work parentTask).1.TaskLinkedOn task.occurrence
        (task.groups.map Execution.DeliveryNode.ref) := by
  have preserve (more : List Task) {current : State}
      (refs : current.GroupRefsUnique)
      (linked : current.TaskLinkedOn task.occurrence
        (task.groups.map Execution.DeliveryNode.ref))
      : (more.foldl State.addTask current).TaskLinkedOn task.occurrence
          (task.groups.map Execution.DeliveryNode.ref) := by
    induction more generalizing current with
    | nil => exact linked
    | cons head rest ih => exact ih (refs.addTask head) (linked.addTask refs head)
  have install (more : List Task) {current : State}
      (refs : current.GroupRefsUnique) (member : task ∈ more)
      : (more.foldl State.addTask current).TaskLinkedOn task.occurrence
          (task.groups.map Execution.DeliveryNode.ref) := by
    induction more generalizing current with
    | nil => cases member
    | cons head rest ih =>
        rcases List.mem_cons.mp member with same | later
        · subst head
          exact preserve rest (refs.addTask task) (current.addTask_links refs task)
        · exact ih (refs.addTask head) later
  exact (install work.tasks (unique.addGroups work.groups) member).addStreams
    work.streams parentTask

/-- If each present candidate is nonempty, pruning removes no nodes and returns only
original candidates. Witness: fuel induction; missing refs are skipped, and the branch
that promotes descendants is impossible. No candidate-presence assumption is needed. -/
theorem State.pruneEmptyGroups_of_nonempty (queue : State)
    (groups : List Execution.DeliveryNode)
    (nonzero
      : ∀ group ∈ groups,
          ∀ node, queue.groupNode? group.ref = some node → node.tasks ≠ [])
    : (queue.pruneEmptyGroups groups).1 = queue
      ∧ (queue.pruneEmptyGroups groups).2.Subset groups := by
  have loop (fuel : Nat) (remaining kept : List Execution.DeliveryNode)
      (positive : ∀ group ∈ remaining, ∀ node,
        queue.groupNode? group.ref = some node → node.tasks ≠ [])
      : (State.pruneEmptyGroups.go fuel queue remaining kept).1 = queue
        ∧ (State.pruneEmptyGroups.go fuel queue remaining kept).2.Subset
            (kept ++ remaining) := by
    induction fuel generalizing remaining kept with
    | zero => exact ⟨rfl, List.subset_append_left _ _⟩
    | succ fuel ih =>
        cases remaining with
        | nil =>
            exact ⟨
              rfl,
              by
                intro node member
                simpa only [State.pruneEmptyGroups.go, List.append_nil] using member
            ⟩
        | cons group rest =>
            have tailPositive := fun next member => positive next (List.mem_cons_of_mem _ member)
            unfold State.pruneEmptyGroups.go
            split
            · obtain ⟨same, subset⟩ := ih rest kept tailPositive
              refine ⟨same, ?_⟩
              intro node member
              rcases List.mem_append.mp (subset member) with old | later
              · exact List.mem_append_left _ old
              · exact List.mem_append_right _ (List.mem_cons_of_mem _ later)
            · rename_i node found
              have notZero := positive group List.mem_cons_self node found
              simpa [notZero, List.append_assoc] using ih rest (kept ++ [group]) tailPositive
  have result := loop (queue.groupNodes.length + groups.length + 1) groups [] nonzero
  refine ⟨result.1, ?_⟩
  intro node member
  have included :=
    result.2 (by simpa only [State.pruneEmptyGroups] using member)
  simpa only [List.nil_append] using included

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
