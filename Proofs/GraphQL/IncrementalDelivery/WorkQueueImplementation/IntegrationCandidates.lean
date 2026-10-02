import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.OwnerAccounting

/-! Fresh integration candidates and their installed task memberships. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- New root candidates come only from parentless group registrations
-----------------------------------------------------------------------------------------

/-- Deduplicating descriptors never introduces a new node.
Witness: membership induction through the first-encounter fold. -/
private theorem mem_distinctDeliveryNodes {nodes : List Execution.DeliveryNode}
    {node : Execution.DeliveryNode} (member : node ∈ distinctDeliveryNodes nodes)
    : node ∈ nodes := by
  have loop (more selected : List Execution.DeliveryNode)
      : ∀ node ∈ more.foldl
          (fun selected node =>
            if selected.any (fun known => known.key == node.key) then selected
            else selected ++ [node]) selected,
          node ∈ selected ++ more := by
    induction more generalizing selected with
    | nil => simp
    | cons head rest ih =>
        intro node member
        simp only [List.foldl_cons] at member
        split at member
        · have prior := ih selected node member
          simp only [List.mem_append, List.mem_cons] at prior ⊢
          exact prior.elim Or.inl (fun later => Or.inr (Or.inr later))
        · have prior := ih (selected ++ [head]) node member
          simpa [List.append_assoc] using prior
  simpa using loop nodes [] node member

/-- Every new group-root candidate is a fresh parentless descriptor from the chunk.
Witness: the registration filter, parent filter, and first-encounter deduplication.
The candidate may later be pruned; this theorem describes the pre-pruning frontier. -/
theorem State.addGroups_newGroup_candidate (queue : State) (groups : List Group)
    {node : Execution.DeliveryNode} (member : node ∈ (queue.addGroups groups).2)
    : ∃ group ∈ groups,
        group.node = node
        ∧ group.parent = none
        ∧ node.key ∉ queue.registeredGroups
        ∧ queue.groupNode? node.key = none := by
  have filtered := mem_distinctDeliveryNodes member
  obtain ⟨group, fresh, selected⟩ := List.mem_filterMap.mp filtered
  obtain ⟨candidate, absent⟩ := List.mem_filter.mp fresh
  cases parent : group.parent with
  | some key => simp [parent] at selected
  | none =>
      have same : group.node = node := by simpa [parent] using selected
      have missing : group.node.key ∉ queue.registeredGroups
          ∧ queue.groupNode? group.node.key = none := by simpa using absent
      exact ⟨group, candidate, same, parent, same ▸ missing⟩

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
    {queue : State} (unique : queue.GroupKeysUnique) (work : Work)
    (parentTask : Option Occurrence := none)
    {task : Task} (member : task ∈ work.tasks)
    : (queue.maybeIntegrateWork work parentTask).1.TaskLinkedOn task.occurrence
        (task.groups.map Execution.DeliveryNode.key) := by
  have preserve (more : List Task) {current : State}
      (keys : current.GroupKeysUnique)
      (linked : current.TaskLinkedOn task.occurrence
        (task.groups.map Execution.DeliveryNode.key))
      : (more.foldl State.addTask current).TaskLinkedOn task.occurrence
          (task.groups.map Execution.DeliveryNode.key) := by
    induction more generalizing current with
    | nil => exact linked
    | cons head rest ih => exact ih (keys.addTask head) (linked.addTask keys head)
  have install (more : List Task) {current : State}
      (keys : current.GroupKeysUnique) (member : task ∈ more)
      : (more.foldl State.addTask current).TaskLinkedOn task.occurrence
          (task.groups.map Execution.DeliveryNode.key) := by
    induction more generalizing current with
    | nil => cases member
    | cons head rest ih =>
        rcases List.mem_cons.mp member with same | later
        · subst head
          exact preserve rest (keys.addTask task) (current.addTask_links keys task)
        · exact ih (keys.addTask head) later
  exact (install work.tasks (unique.addGroups work.groups) member).addStreams
    work.streams parentTask

/-- If each present candidate is nonempty, pruning removes no nodes and returns only
original candidates. Witness: fuel induction; missing keys are skipped, and the branch
that promotes descendants is impossible. No candidate-presence assumption is needed. -/
theorem State.pruneEmptyGroups_of_nonempty (queue : State)
    (groups : List Execution.DeliveryNode)
    (nonzero
      : ∀ group ∈ groups,
          ∀ node, queue.groupNode? group.key = some node → node.tasks ≠ [])
    : (queue.pruneEmptyGroups groups).1 = queue
      ∧ (queue.pruneEmptyGroups groups).2.Subset groups := by
  have loop (fuel : Nat) (remaining kept : List Execution.DeliveryNode)
      (positive : ∀ group ∈ remaining, ∀ node,
        queue.groupNode? group.key = some node → node.tasks ≠ [])
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
  simpa only [State.pruneEmptyGroups, List.nil_append]
    using loop (queue.groupNodes.length + groups.length + 1) groups [] nonzero

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
