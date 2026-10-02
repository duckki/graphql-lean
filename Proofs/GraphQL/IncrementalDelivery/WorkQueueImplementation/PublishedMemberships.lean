import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupPublication
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.DrainAccounting
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.PublicationInventory
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ActiveLinks

/-! Flushing an occurrence removes its membership from every shared contributor. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (ExecutionGroupValue WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Membership exclusion concerns group records, not only the stored-value map
-----------------------------------------------------------------------------------------

/-- No live group record retains `occurrence` in its task-membership list. -/
def State.TaskMembershipAbsent (queue : State) (occurrence : Occurrence) : Prop :=
  ∀ node ∈ queue.groupNodes, occurrence ∉ node.tasks

/-- Removing any task preserves an already absent membership.
Witness: every surviving task list is a filter of its original list.
-/
theorem State.TaskMembershipAbsent.removeTask {queue : State} {occurrence}
    (absent : queue.TaskMembershipAbsent occurrence) (removed : Occurrence)
    : (queue.removeTask removed).TaskMembershipAbsent occurrence := by
  intro node member task
  obtain ⟨old, prior, rfl⟩ := List.mem_map.mp member
  exact absent old prior (List.mem_filter.mp task).1

/-- Removing a task clears all of its shared group memberships, including duplicates.
Witness: the same occurrence filter is applied to every live group record.
-/
theorem State.removeTask_membershipAbsent (queue : State) (occurrence : Occurrence)
    : (queue.removeTask occurrence).TaskMembershipAbsent occurrence := by
  intro node member task
  obtain ⟨old, prior, rfl⟩ := List.mem_map.mp member
  have different := (List.mem_filter.mp task).2
  simp [bne, (occurrence_beq_iff_eq occurrence occurrence).mpr rfl] at different

/-- Empty-shell pruning cannot reintroduce a previously absent task membership.
Witness: its pointwise record-preservation theorem; promoted notices do not mutate lists.
-/
theorem State.TaskMembershipAbsent.pruneEmptyGroups {queue : State} {occurrence}
    (absent : queue.TaskMembershipAbsent occurrence) (groups)
    : (queue.pruneEmptyGroups groups).1.TaskMembershipAbsent occurrence := by
  exact State.pruneEmptyGroups_nodeProperty (fun node => occurrence ∉ node.tasks) absent groups

/-- The complete task flush preserves all earlier membership exclusions.
Witness: each selected task is removed globally; a missing lookup changes nothing.
-/
theorem State.TaskMembershipAbsent.flushGroupTasks {queue : State} {occurrence}
    (absent : queue.TaskMembershipAbsent occurrence) (tasks : List Occurrence)
    (values : List ExecutionGroupValue) (streams : Keys)
    : (tasks.foldl flushGroupTask (queue, values, streams)).1.TaskMembershipAbsent
        occurrence := by
  induction tasks generalizing queue values streams with
  | nil => exact absent
  | cons task rest ih =>
      simp only [List.foldl_cons, flushGroupTask]
      split
      · exact ih absent _ _
      · exact ih (absent.removeTask task) _ _

/-- An initially findable selected task is absent from every group after the flush.
Witness: its first selected occurrence removes it globally. Earlier different removals
preserve its exact lookup, and the remaining loop preserves the exclusion. No source,
key uniqueness, distinct membership, or already-admitted-history premise is needed.
-/
theorem flushGroupTask_membershipAbsent {queue : State} {tasks : List Occurrence}
    (values : List ExecutionGroupValue) (streams : Keys) {occurrence node}
    (member : occurrence ∈ tasks) (found : queue.taskNode? occurrence = some node)
    : (tasks.foldl flushGroupTask (queue, values, streams)).1.TaskMembershipAbsent
        occurrence := by
  induction tasks generalizing queue values streams with
  | nil => cases member
  | cons head rest ih =>
      by_cases same : occurrence = head
      · subst head
        simp only [List.foldl_cons, flushGroupTask, found]
        exact (queue.removeTask_membershipAbsent occurrence).flushGroupTasks rest _ _
      · have later := (List.mem_cons.mp member).resolve_left same
        simp only [List.foldl_cons, flushGroupTask]
        split
        · exact ih _ _ later found
        · apply ih _ _ later
          rwa [queue.removeTask_lookup_other same]

-----------------------------------------------------------------------------------------
-- Successful closure keeps that exclusion through group removal and child promotion
-----------------------------------------------------------------------------------------

/-- Successful closure preserves exclusions established by earlier publications.
Witness: task removal, filtering the closed owner, and pruning can only remove memberships.
-/
theorem State.TaskMembershipAbsent.finishGroupSuccess {queue : State} {occurrence}
    (absent : queue.TaskMembershipAbsent occurrence) (group : GroupNode)
    : (queue.finishGroupSuccess group).1.TaskMembershipAbsent occurrence := by
  have flushed := absent.flushGroupTasks group.tasks [] []
  let values := group.tasks.foldl flushGroupTask (queue, [], [])
  let current : State := { values.1 with
    groupNodes := values.1.groupNodes.filter
      (fun node => node.group.node.key != group.group.node.key)
    rootGroups := values.1.rootGroups.filter (· != group.group.node.key) }
  have removed : current.TaskMembershipAbsent occurrence :=
    fun node member => flushed node (List.mem_filter.mp member).1
  exact removed.pruneEmptyGroups _

/-- A flushed membership cannot remain in a child or any other surviving co-owner.
Witness: the actual findable-task selection removes the occurrence from every group's
list before the closing owner is removed and taskless child wrappers are pruned.
This supplies local publication exclusion for the kept-notice contents bridge.
-/
theorem State.finishGroupSuccess_membershipAbsent {queue : State} (group : GroupNode)
    {occurrence node} (member : occurrence ∈ group.tasks)
    (found : queue.taskNode? occurrence = some node)
    : (queue.finishGroupSuccess group).1.TaskMembershipAbsent occurrence := by
  have flushed := flushGroupTask_membershipAbsent [] [] member found
  let values := group.tasks.foldl flushGroupTask (queue, [], [])
  let current : State := { values.1 with
    groupNodes := values.1.groupNodes.filter
      (fun node => node.group.node.key != group.group.node.key)
    rootGroups := values.1.rootGroups.filter (· != group.group.node.key) }
  have removed : current.TaskMembershipAbsent occurrence :=
    fun node member => flushed node (List.mem_filter.mp member).1
  exact removed.pruneEmptyGroups _

/-- Any selected stored node's occurrence is removed from all surviving memberships.
Witness: its original task-map membership ensures a successful lookup, even when raw
task nodes duplicate an occurrence. The flush's selection premise places it on the list.
-/
theorem State.finishGroupSuccess_selectedMembershipAbsent {queue : State}
    (group : GroupNode) {node : TaskNode} (known : node ∈ queue.taskNodes)
    (selected : node.task.occurrence ∈ group.tasks)
    : (queue.finishGroupSuccess group).1.TaskMembershipAbsent node.task.occurrence := by
  cases found : queue.taskNode? node.task.occurrence with
  | none =>
      have impossible := List.find?_eq_none.mp found node known
      simp [(occurrence_beq_iff_eq node.task.occurrence node.task.occurrence).mpr rfl]
        at impossible
  | some task => exact queue.finishGroupSuccess_membershipAbsent group selected found

/-- The same exact publication ledger also excludes old and newly delivered memberships.
Witness: reuse the flush's existing selected-node witness and inventory proof, then show
each selected stored value's occurrence is removed globally. No independently chosen
publication sequence or stronger event/source premise is introduced.
-/
theorem State.PublicationInventory.finishGroupSuccess_memberships
    {queue : State} {property published}
    (inventory : queue.PublicationInventory property published)
    (absent : ∀ publication ∈ published, queue.TaskMembershipAbsent publication.1)
    (group : GroupNode)
    : ∃ added : List ObjectPublication,
        added.map Prod.snd
          = (queue.finishGroupSuccess group).2.1.flatMap WorkQueueEvent.objectValues
        ∧ (queue.finishGroupSuccess group).1.PublicationInventory property
            (published ++ added)
        ∧ ∀ publication ∈ published ++ added,
            (queue.finishGroupSuccess group).1.TaskMembershipAbsent publication.1 := by
  obtain ⟨selected, unique, known, events, retained, removed⟩ :=
    queue.finishGroupSuccess_publications group
  obtain ⟨values, next⟩ := inventory.finishGroupSuccess_selected group selected unique known
    events retained removed
  refine ⟨storedPublications selected, values, next, ?_⟩
  intro publication member
  rcases List.mem_append.mp member with old | new
  · exact (absent publication old).finishGroupSuccess group
  · obtain ⟨node, included, occurrenceEq, _⟩ := storedPublications_member new
    rw [← occurrenceEq]
    exact queue.finishGroupSuccess_selectedMembershipAbsent group
      (known node included).1 (known node included).2

/-- Activating released roots starts computations but leaves group memberships unchanged.
Witness: the exact group-core projection of `startNewWork`.
-/
theorem State.TaskMembershipAbsent.startNewWork {queue : State} {occurrence}
    (absent : queue.TaskMembershipAbsent occurrence) (newWork : NewWork)
    : (queue.startNewWork newWork).TaskMembershipAbsent occurrence := by
  intro node member
  rw [(queue.startNewWork_groupCore newWork).1] at member
  exact absent node member

/-- Cancelling a group only removes records and cannot restore delivered memberships.
Witness: surviving records belong to the original group-node map.
-/
theorem State.TaskMembershipAbsent.removeGroup {queue : State} {occurrence}
    (absent : queue.TaskMembershipAbsent occurrence) (key : Nat)
    : (queue.removeGroup key).TaskMembershipAbsent occurrence :=
  fun node member => absent node (List.mem_filter.mp member).1

/-- Every bounded drain prefix preserves any earlier publication's membership exclusion.
Witness: successful flushing and activation preserve the absent membership; failed
closure only removes records. The induction does not select a publication ledger.
-/
theorem State.TaskMembershipAbsent.drainReadyGroups_go {queue : State} {occurrence}
    (absent : queue.TaskMembershipAbsent occurrence) (fuel : Nat)
    : (State.drainReadyGroups.go fuel queue).1.TaskMembershipAbsent occurrence := by
  induction fuel generalizing queue with
  | zero => exact absent
  | succ fuel ih =>
      unfold State.drainReadyGroups.go
      dsimp only
      split
      · exact absent
      · rename_i node selected
        cases cached : node.failure with
        | none => exact ih ((absent.finishGroupSuccess node).startNewWork _)
        | some errors => exact ih (absent.removeGroup _)

/-- The full recursive drain retains membership exclusion on its one publication ledger.
Witness: success adds its actual selected values and removes their shared memberships;
activation preserves exclusions, and failure removes records without adding values.
All internal successful releases use the same growing ledger, including immediate drains
of children promoted through taskless wrappers.
-/
theorem State.PublicationInventory.drainReadyGroups_memberships
    {queue : State} {property published}
    (inventory : queue.PublicationInventory property published)
    (absent : ∀ publication ∈ published, queue.TaskMembershipAbsent publication.1)
    : ∃ added : List ObjectPublication,
        added.map Prod.snd = queue.drainReadyGroups.2.flatMap WorkQueueEvent.objectValues
        ∧ queue.drainReadyGroups.1.PublicationInventory property (published ++ added)
        ∧ ∀ publication ∈ published ++ added,
            queue.drainReadyGroups.1.TaskMembershipAbsent publication.1 := by
  have loop (fuel : Nat) (current : State) (priorPublished : List ObjectPublication)
      (prior : current.PublicationInventory property priorPublished)
      (excluded : ∀ publication ∈ priorPublished, current.TaskMembershipAbsent publication.1)
      : ∃ added : List ObjectPublication,
          added.map Prod.snd
            = (State.drainReadyGroups.go fuel current).2.flatMap WorkQueueEvent.objectValues
          ∧ (State.drainReadyGroups.go fuel current).1.PublicationInventory property
              (priorPublished ++ added)
          ∧ ∀ publication ∈ priorPublished ++ added,
              (State.drainReadyGroups.go fuel current).1.TaskMembershipAbsent
                publication.1 := by
    induction fuel generalizing current priorPublished with
    | zero =>
        exact ⟨
          [],
          rfl,
          by simpa [State.drainReadyGroups.go] using prior,
          by simpa [State.drainReadyGroups.go] using excluded
        ⟩
    | succ fuel ih =>
        unfold State.drainReadyGroups.go
        dsimp only
        split
        · exact ⟨[], rfl, by simpa using prior, by simpa using excluded⟩
        · rename_i node selected
          cases cached : node.failure with
          | none =>
              obtain ⟨first, firstValues, flushed, removed⟩ :=
                prior.finishGroupSuccess_memberships excluded node
              obtain ⟨later, laterValues, final, excluded⟩ := ih _ _
                ⟨flushed.unique, flushed.provenance,
                  flushed.stored.startNewWork (current.finishGroupSuccess node).2.2⟩
                (fun publication member =>
                  (removed publication member).startNewWork (current.finishGroupSuccess node).2.2)
              refine ⟨first ++ later, ?_, ?_, ?_⟩
              · simp only [List.map_append, List.flatMap_append, firstValues, laterValues]
              · simpa only [List.append_assoc] using final
              · simpa only [List.append_assoc] using excluded
          | some errors =>
              obtain ⟨added, values, final, absent⟩ := ih _ _
                ⟨prior.unique, prior.provenance, prior.stored.removeGroup _⟩
                (fun publication member => (excluded publication member).removeGroup _)
              refine ⟨added, ?_, final, absent⟩
              simpa only [State.finishGroupFailure, List.flatMap_append,
                List.flatMap_singleton, WorkQueueEvent.objectValues, List.nil_append] using values
  exact loop _ queue published inventory absent

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
