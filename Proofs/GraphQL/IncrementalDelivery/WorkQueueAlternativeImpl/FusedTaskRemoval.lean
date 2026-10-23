import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.PruningTaskOwnership
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.TaskRejections

/-! Task ownership progress follows the exact fused-removal trace, including unstarted work. -/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
open GraphQL.IncrementalDelivery.WorkQueueSemantics (Occurrence)
open GraphQL.IncrementalDelivery.ReferenceWorkQueue (Task)

private abbrev Kernel := ReferenceWorkQueue.State

-----------------------------------------------------------------------------------------
-- The actual task fold cannot silently dispose the selected occurrence
-----------------------------------------------------------------------------------------

/-- Task pruning preserves every retained rejection fact. -/
theorem PruningTasks.taskRejections {queue occurrences final targets property}
    (trace : PruningTasks queue occurrences final targets)
    (prior : queue.TaskRejectionsSatisfy property)
    : final.TaskRejectionsSatisfy property := by
  induction trace with
  | nil => exact prior
  | missing _ _ ih | shared _ _ _ ih => exact ih prior
  | dispose _ _ _ ih => exact ih (prior.removeTask _)

/-- Group pruning preserves every retained rejection fact. -/
theorem PruningGroups.taskRejections {queue pending final targets property}
    (trace : PruningGroups queue pending final targets)
    (prior : queue.TaskRejectionsSatisfy property)
    : final.TaskRejectionsSatisfy property := by
  induction trace with
  | nil => exact prior
  | missing _ _ ih => exact ih prior
  | visit _ tasks _ ih => exact ih (tasks.taskRejections prior)

/-- A task fold preserves this occurrence's memberships or requests its actual abort. -/
theorem PruningTasks.linkedOnOrAbort {queue occurrences final targets occurrence keys}
    (trace : PruningTasks queue occurrences final targets)
    (links : queue.TaskLinkedOn occurrence keys)
    (unrejected : queue.TaskRejectionsSatisfy (fun rejected _ => rejected ≠ occurrence))
    : final.TaskLinkedOn occurrence keys ∨ .task occurrence ∈ targets := by
  induction trace with
  | nil => exact Or.inl links
  | missing _ _ ih | shared _ _ _ ih => exact ih links unrejected
  | @dispose task rest final targets queue chosen found ownerless trace ih =>
      by_cases same : occurrence = chosen
      · subst chosen
        right
        apply List.mem_append_left
        simp only [State.cancelTask, unrejected.unrejected_lookup,
          Bool.false_eq_true, ↓reduceIte]
        exact List.mem_append_left _ List.mem_cons_self
      · rcases ih (links.removeOtherTask chosen same) (unrejected.removeTask chosen) with kept | aborted
        · exact Or.inl kept
        · exact Or.inr (List.mem_append_right _ aborted)

/-- A selected task whose every owner is absent receives an abort even if unstarted. -/
theorem PruningTasks.ownerlessSelected_aborted
    {queue occurrences final targets occurrence task}
    (trace : PruningTasks queue occurrences final targets)
    (selected : occurrence ∈ occurrences) (catalogue : queue.task? occurrence = some task)
    (ownerless : ∀ owner ∈ task.groups, queue.groupNode? owner.ref = none)
    (unrejected : queue.TaskRejectionsSatisfy (fun rejected _ => rejected ≠ occurrence))
    : .task occurrence ∈ targets := by
  induction trace with
  | nil => cases selected
  | @missing queue rest final targets chosen absent trace ih =>
      rcases List.mem_cons.mp selected with same | later
      · subst chosen; rw [absent] at catalogue; contradiction
      · exact ih later catalogue ownerless unrejected
  | @shared found queue rest final targets chosen lookup retained trace ih =>
      rcases List.mem_cons.mp selected with same | later
      · subst chosen
        cases Option.some.inj (lookup.symm.trans catalogue)
        have all : task.groups.all (fun owner => (queue.groupNode? owner.ref).isNone) = true :=
          List.all_eq_true.mpr (fun owner member => by simp [ownerless owner member])
        rw [all] at retained
        contradiction
      · exact ih later catalogue ownerless unrejected
  | @dispose found rest final targets queue chosen lookup owners trace ih =>
      rcases List.mem_cons.mp selected with same | later
      · subst chosen
        apply List.mem_append_left
        simp only [State.cancelTask, unrejected.unrejected_lookup,
          Bool.false_eq_true, ↓reduceIte]
        exact List.mem_append_left _ List.mem_cons_self
      · apply List.mem_append_right
        apply ih later catalogue ?_ (unrejected.removeTask chosen)
        intro owner member
        cases live : (queue.removeTask chosen).groupNode? owner.ref with
        | none => rfl
        | some node =>
            obtain ⟨old, earlier, _⟩ := queue.removeTask_groupEdgesFrom chosen owner.ref node live
            rw [ownerless owner member] at earlier
            contradiction

-----------------------------------------------------------------------------------------
-- Exhaustive group traversal retains an owner or requests the task
-----------------------------------------------------------------------------------------

private abbrev withoutGroup (queue : Kernel) (key : Nat) : Kernel :=
  {
    queue with
      groupNodes := queue.groupNodes.filter (fun node => node.group.node.ref != key)
      rootGroups := queue.rootGroups.filter (· != key)
  }

/-- The exact dynamic group walk retains a live contributing owner or aborts the task.
Membership completeness forces the last-owner occurrence into the disposal fold. Permanent
catalogue lookup supplies the owner test; no started-node or native inventory is required.
-/
theorem PruningGroups.linkedOwnerOrAbort {queue pending final targets occurrence task}
    (trace : PruningGroups queue pending final targets)
    (links : queue.TaskLinkedOn occurrence (task.groups.map Execution.DeliveryNode.ref))
    (catalogue : queue.task? occurrence = some task)
    (owned : ∃ owner ∈ task.groups, ∃ group, queue.groupNode? owner.ref = some group)
    (unrejected : queue.TaskRejectionsSatisfy (fun rejected _ => rejected ≠ occurrence))
    : (∃ owner ∈ task.groups, ∃ group, final.groupNode? owner.ref = some group)
      ∨ .task occurrence ∈ targets := by
  induction trace with
  | nil => exact Or.inl owned
  | missing _ _ ih => exact ih links catalogue owned unrejected
  | @visit group queue key current first keys final later lookup tasks rest ih =>
      have currentCatalogue : current.task? occurrence = some task := (tasks.taskLookup occurrence).trans catalogue
      have filteredLinks : (withoutGroup queue key).TaskLinkedOn occurrence
          (task.groups.map Execution.DeliveryNode.ref) :=
        fun owner member contributes => links owner (List.mem_filter.mp member).1 contributes
      rcases tasks.linkedOnOrAbort filteredLinks unrejected with currentLinks | aborted
      · by_cases currentOwned :
          ∃ owner ∈ task.groups, ∃ group, current.groupNode? owner.ref = some group
        · rcases ih currentLinks currentCatalogue currentOwned (tasks.taskRejections unrejected) with kept | aborted
          · exact Or.inl kept
          · exact Or.inr (List.mem_append_right _ aborted)
        · have ownerless : ∀ owner ∈ task.groups, (withoutGroup queue key).groupNode? owner.ref = none := by
            intro owner member
            cases live : (withoutGroup queue key).groupNode? owner.ref with
            | none => rfl
            | some old =>
                obtain ⟨new, kept⟩ := tasks.groupPresent ⟨old, live⟩
                exact False.elim (currentOwned ⟨owner, member, new, kept⟩)
          obtain ⟨owner, contributes, old, live⟩ := owned
          have same : owner.ref = key := by
            by_cases equal : owner.ref = key
            · exact equal
            apply False.elim
            have filtered : (withoutGroup queue key).groupNode? owner.ref = some old := by
              change (queue.groupNodes.filter (fun node => node.group.node.ref != key)).find?
                (fun node => node.group.node.ref == owner.ref) = some old
              rw [ReferenceWorkQueue.State.groupNode?_filterRefs queue (fun other => other != key)]
              simpa [equal] using live
            rw [ownerless owner contributes] at filtered
            contradiction
          have linked : occurrence ∈ group.tasks := links group (List.mem_of_find?_eq_some lookup)
            (List.mem_map.mpr ⟨owner, contributes,
              same.trans (ReferenceWorkQueue.State.groupNode?_ref lookup).symm⟩)
          exact Or.inr
            (List.mem_append_left _
              (tasks.ownerlessSelected_aborted linked catalogue ownerless unrejected))
      · exact Or.inr (List.mem_append_left _ aborted)

/-- The actual trace preserves complete contributor links or includes this task's abort. -/
theorem PruningGroups.linkedOnOrAbort {queue pending final targets occurrence keys}
    (trace : PruningGroups queue pending final targets)
    (links : queue.TaskLinkedOn occurrence keys)
    (unrejected : queue.TaskRejectionsSatisfy (fun rejected _ => rejected ≠ occurrence))
    : final.TaskLinkedOn occurrence keys ∨ .task occurrence ∈ targets := by
  induction trace with
  | nil => exact .inl links
  | missing _ _ ih => exact ih links unrejected
  | @visit group queue key current first more final later found tasks rest ih =>
      have filtered : (withoutGroup queue key).TaskLinkedOn occurrence keys := fun group member contributes =>
        links group (List.mem_filter.mp member).1 contributes
      rcases tasks.linkedOnOrAbort filtered unrejected with current | requested
      · rcases ih current (tasks.taskRejections unrejected) with kept | later
        · exact .inl kept
        · exact .inr (List.mem_append_right _ later)
      · exact .inr (List.mem_append_left _ requested)

/-- Literal single-root removal keeps a catalogue task's live owner and links, or emits
its actual abort. This covers unstarted tasks as well as stored/active records; acquired
native inventories and asynchronous cleanup are separate observations.
-/
def FusedRemovalTaskProgress : Prop :=
  ∀ (state : State) (root : Nat) (task : ReferenceWorkQueue.Task)
    (initial : List CleanupTarget),
    initial.Nodup
    → state.queue.task? task.occurrence = some task
    → state.queue.TaskLinkedOn task.occurrence
        (task.groups.map Execution.DeliveryNode.ref)
    → (∃ owner ∈ task.groups, ∃ group, state.queue.groupNode? owner.ref = some group)
    → state.queue.TaskRejectionsSatisfy (fun rejected _ => rejected ≠ task.occurrence)
    → let reduced := state.removeGroup root initial
      (reduced.1.queue.TaskLinkedOn task.occurrence
          (task.groups.map Execution.DeliveryNode.ref)
        ∧ ∃ owner ∈ task.groups,
            ∃ group, reduced.1.queue.groupNode? owner.ref = some group)
      ∨ .abortTask task.occurrence ∈ reduced.2.flatMap CleanupTarget.effects

theorem FusedRemovalTaskProgress_holds : FusedRemovalTaskProgress := by
  intro state root task initial unique catalogue links owned unrejected
  obtain ⟨final, targets, trace, cleanup, groups, _records⟩ := pruningRemoval_witness state root initial unique
  have aborted (requested : CleanupTarget.task task.occurrence ∈ targets)
      : HostEffect.abortTask task.occurrence ∈ (state.removeGroup root initial).2.flatMap CleanupTarget.effects := by
    have target : CleanupTarget.task task.occurrence ∈ (state.removeGroup root initial).2 := by
      rw [cleanup, mem_uniqueCleanupTargets]
      exact List.mem_append_right _ requested
    exact List.mem_flatMap.mpr ⟨.task task.occurrence, target, List.mem_cons_self⟩
  rcases trace.linkedOnOrAbort links unrejected with retained | requested
  · rcases trace.linkedOwnerOrAbort links catalogue owned unrejected with live | requested
    · apply Or.inl
      refine ⟨?_, ?_⟩
      · intro group member contributes
        rw [groups] at member
        exact retained group member contributes
      · obtain ⟨owner, member, group, found⟩ := live
        refine ⟨owner, member, group, ?_⟩
        change (state.removeGroup root initial).1.queue.groupNodes.find? _ = some group
        rw [groups]
        exact found
    · exact .inr (aborted requested)
  · exact .inr (aborted requested)

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
