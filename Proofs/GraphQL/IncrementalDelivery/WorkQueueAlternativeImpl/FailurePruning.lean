import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.FusedRemovalBookkeeping
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.FusedResourceRemoval
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.RegistrationSnapshotProjection
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupPublication

/-! Proof-side traces of the actual fused removal. Raw trace targets retain each pre-unlinking
boundary; the real reduction deduplicates the same targets in first-encounter order.
The registration/publication-filtered view at the end is topology evidence only, not an
algorithm that infers actual cleanup effects from wire notices.
-/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
open GraphQL.IncrementalDelivery.WorkQueueSemantics (NodeRefs Occurrence)
open GraphQL.IncrementalDelivery.ReferenceWorkQueue (Task TaskNode GroupNode)

private abbrev Kernel := ReferenceWorkQueue.State

-----------------------------------------------------------------------------------------
-- Trace the literal task fold, retaining its pre-unlinking disposal boundary
-----------------------------------------------------------------------------------------

/-- The fold's mathematical trace records raw cleanup targets before unlinking.
The actual accumulator deduplicates these identities without losing or reordering first
encounters. Missing tasks and surviving co-owners do not enter the disposal constructor.
-/
inductive PruningTasks
    : Kernel → List Occurrence → Kernel → List CleanupTarget → Prop where
  | nil (queue) : PruningTasks queue [] queue []
  | missing (absent : queue.task? occurrence = none)
    (rest : PruningTasks queue occurrences final targets)
    : PruningTasks queue (occurrence :: occurrences) final targets
  | shared (found : queue.task? occurrence = some task)
    (retained
      : task.groups.all (fun owner => (queue.groupNode? owner.ref).isNone) = false)
    (rest : PruningTasks queue occurrences final targets)
    : PruningTasks queue (occurrence :: occurrences) final targets
  | dispose (found : queue.task? occurrence = some task)
    (ownerless
      : task.groups.all (fun owner => (queue.groupNode? owner.ref).isNone) = true)
    (rest : PruningTasks (queue.removeTask occurrence) occurrences final targets)
    : PruningTasks queue (occurrence :: occurrences) final
        (({ queue } : State).cancelTask occurrence ++ targets)

private theorem pruningTasks_witness (state : State) (occurrences : List Occurrence)
    (initial : List CleanupTarget) (unique : initial.Nodup)
    : ∃ current targets,
        occurrences.foldl fusedRemovalTaskStep (state, initial)
          = (current, uniqueCleanupTargets (initial ++ targets))
        ∧ PruningTasks state.queue occurrences current.queue targets := by
  induction occurrences generalizing state initial with
  | nil =>
      exact ⟨state, [], by simp [uniqueCleanupTargets_eq_self initial unique], .nil _⟩
  | cons occurrence rest ih =>
      cases found : state.queue.task? occurrence with
      | none =>
          obtain ⟨current, targets, same, trace⟩ := ih state initial unique
          exact ⟨
            current,
            targets,
            by simpa [fusedRemovalTaskStep, found] using same,
            .missing found trace
          ⟩
      | some task =>
          cases ownerless
                : task.groups.all
                    (fun owner => (state.queue.groupNode? owner.ref).isNone) with
          | false =>
              obtain ⟨current, targets, same, trace⟩ := ih state initial unique
              exact ⟨
                current,
                targets,
                by simpa [fusedRemovalTaskStep, found, ownerless] using same,
                .shared found ownerless trace
              ⟩
          | true =>
              obtain ⟨current, targets, same, trace⟩ := ih
                { state with queue := state.queue.removeTask occurrence }
                (uniqueCleanupTargets (initial ++ state.cancelTask occurrence))
                (uniqueCleanupTargets_nodup _)
              refine ⟨current, state.cancelTask occurrence ++ targets, ?_,
                .dispose found ownerless trace⟩
              simp only [List.foldl_cons, fusedRemovalTaskStep, found, ownerless, ↓reduceIte]
              rw [same, uniqueCleanupTargets_unique_append, List.append_assoc]

/-- Task disposal changes memberships, never the number of live group records. -/
theorem PruningTasks.groupCount {queue occurrences final targets}
    (trace : PruningTasks queue occurrences final targets)
    : final.groupNodes.length = queue.groupNodes.length := by
  induction trace with
  | nil => rfl
  | missing _ _ ih | shared _ _ _ ih => exact ih
  | dispose _ _ _ ih => simpa [ReferenceWorkQueue.State.removeTask] using ih

/-- A held source either retains its exact task record or is requested before unlinking. -/
theorem PruningTasks.heldSource {queue occurrences final targets}
    (trace : PruningTasks queue occurrences final targets)
    {occurrence : Occurrence} {node : TaskNode} {key : Nat}
    (found : queue.taskNode? occurrence = some node) (held : key ∈ node.childStreams)
    : final.taskNode? occurrence = some node ∨ .stream key ∈ targets := by
  induction trace with
  | nil => exact Or.inl found
  | missing _ _ ih | shared _ _ _ ih => exact ih found
  | @dispose task rest final targets queue selected lookup owners trace ih =>
      by_cases same : occurrence = selected
      · subst selected
        right
        apply List.mem_append_left
        simp only [State.cancelTask, found, Option.toList_some, List.flatMap_cons,
          List.flatMap_nil, List.append_nil, List.mem_append]
        exact Or.inr (List.mem_map.mpr ⟨key, held, rfl⟩)
      · rcases ih ((queue.removeTask_lookup_other same).trans found) with kept | requested
        · exact Or.inl kept
        · exact Or.inr (List.mem_append_right _ requested)

-----------------------------------------------------------------------------------------
-- The dynamically shrinking actual walk exhausts its supplied frontier
-----------------------------------------------------------------------------------------

private abbrev withoutGroup (queue : Kernel) (key : Nat) : Kernel :=
  {
    queue with
      groupNodes := queue.groupNodes.filter (fun node => node.group.node.ref != key)
      rootGroups := queue.rootGroups.filter (· != key)
  }

/-- Exhaustive trace of the effect traversal. There is no fuel-exhausted constructor:
the executable initial budget is enough even for raw cycles/shared/stale child links,
because this walk removes each live record before traversing its children.
-/
inductive PruningGroups : Kernel → NodeRefs → Kernel → List CleanupTarget → Prop where
  | nil (queue) : PruningGroups queue [] queue []
  | missing (absent : queue.groupNode? key = none)
    (rest : PruningGroups queue keys final targets)
    : PruningGroups queue (key :: keys) final targets
  | visit (found : queue.groupNode? key = some group)
    (tasks : PruningTasks (withoutGroup queue key) group.tasks current first)
    (rest : PruningGroups current (group.childGroups ++ keys) final later)
    : PruningGroups queue (key :: keys) final (first ++ later)

private theorem withoutGroup_length {queue : Kernel} {key : Nat} {group : GroupNode}
    (found : queue.groupNode? key = some group)
    : (withoutGroup queue key).groupNodes.length < queue.groupNodes.length := by
  apply List.length_filter_lt_length_iff_exists.mpr
  refine ⟨group, List.mem_of_find?_eq_some found, ?_⟩
  simp [ReferenceWorkQueue.State.groupNode?_ref found]

/-- One trace identifies the real walker endpoint and its deduplicated cumulative targets.
Missing keys consume no live-node budget; removing a found record justifies the recursive
budget even on raw cycles, shared child links and stale memberships.
-/
theorem pruningGroups_witness (fuel : Nat) (state : State) (pending removed : NodeRefs)
    (initial : List CleanupTarget) (unique : initial.Nodup)
    (budget : state.queue.groupNodes.length < fuel)
    : ∃ current retired targets,
        State.removeGroup.walk fuel state pending removed initial
          = (current, retired, uniqueCleanupTargets (initial ++ targets))
        ∧ PruningGroups state.queue pending current.queue targets := by
  induction fuel generalizing state pending removed initial with
  | zero => omega
  | succ fuel ih =>
      induction pending generalizing state removed initial with
      | nil =>
          exact ⟨
            state,
            removed,
            [],
            by simp [State.removeGroup.walk, uniqueCleanupTargets_eq_self initial unique],
            .nil _
          ⟩
      | cons key rest tailIH =>
          cases found : state.queue.groupNode? key with
          | none =>
              obtain ⟨current, retired, targets, same, trace⟩ := tailIH state removed initial unique budget
              exact ⟨
                current,
                retired,
                targets,
                by simpa [State.removeGroup.walk, found] using same,
                .missing found trace
              ⟩
          | some group =>
              obtain ⟨current, first, folded, tasks⟩ :=
                pruningTasks_witness (eraseRemovalGroup state key) group.tasks initial unique
              have shrinks := withoutGroup_length found
              have count := tasks.groupCount
              have enough : current.queue.groupNodes.length < fuel := by
                change current.queue.groupNodes.length
                  = (withoutGroup state.queue key).groupNodes.length at count
                omega
              obtain ⟨final, retired, later, walked, trace⟩ := ih current
                (group.childGroups ++ rest) (key :: removed)
                (uniqueCleanupTargets (initial ++ first)) (uniqueCleanupTargets_nodup _) enough
              refine ⟨final, retired, first ++ later, ?_, .visit found tasks trace⟩
              rw [State.removeGroup.walk, found]
              change State.removeGroup.walk fuel
                (group.tasks.foldl fusedRemovalTaskStep (eraseRemovalGroup state key, initial)).1
                (group.childGroups ++ rest) (key :: removed)
                (group.tasks.foldl fusedRemovalTaskStep (eraseRemovalGroup state key, initial)).2 = _
              rw [folded, walked, uniqueCleanupTargets_unique_append, List.append_assoc]

/-- Wrapper bookkeeping changes no group/task record. The exact actual cleanup list comes
from this same trace, not a second output-driven traversal.
-/
theorem pruningRemoval_witness (state : State) (root : Nat)
    (initial : List CleanupTarget := []) (unique : initial.Nodup := by simp)
    : ∃ final targets,
        PruningGroups state.queue [root] final targets
        ∧ (state.removeGroup root initial).2 = uniqueCleanupTargets (initial ++ targets)
        ∧ (state.removeGroup root initial).1.queue.groupNodes = final.groupNodes
        ∧ (state.removeGroup root initial).1.queue.taskNodes = final.taskNodes := by
  obtain ⟨current, retired, targets, same, trace⟩ :=
    pruningGroups_witness (state.queue.groupNodes.length + 1) state [root] [] initial
      unique (by omega)
  refine ⟨current.queue, targets, trace, ?_, ?_, ?_⟩
  all_goals simp only [State.removeGroup, same]

/-- Group pruning cannot forget a looked-up held source without a corresponding request. -/
theorem PruningGroups.heldSource {queue pending final targets}
    (trace : PruningGroups queue pending final targets)
    {occurrence : Occurrence} {node : TaskNode} {key : Nat}
    (found : queue.taskNode? occurrence = some node) (held : key ∈ node.childStreams)
    : final.taskNode? occurrence = some node ∨ .stream key ∈ targets := by
  induction trace with
  | nil => exact Or.inl found
  | missing _ _ ih => exact ih found
  | visit _ tasks rest ih =>
      rcases tasks.heldSource found held with kept | requested
      · rcases ih kept with retained | later
        · exact Or.inl retained
        · exact Or.inr (List.mem_append_right _ later)
      · exact Or.inr (List.mem_append_left _ requested)

-----------------------------------------------------------------------------------------
-- A proof-only publication-filtered topology view for legacy path transport
-----------------------------------------------------------------------------------------

/-- Registration-phase topology with successfully published keys excluded.
This is proof evidence for ownership/path transport, not the runtime input to removal and
not a source of actual cleanup effects. Handler disposal must use the real reduction.
-/
def failurePruningView (before : Kernel) (event : GraphEvent)
    (events : List Execution.WorkQueueEvent)
    : Kernel :=
  let snapshot := registrationSnapshot before event
  let published :=
    events.filterMap
      fun
      | .groupSuccess group _ _ => some group.ref
      | _ => none
  let pending :=
    fun occurrence =>
      let settling :=
        match event with
        | .taskFailure task _ => task == occurrence
        | _ => false
      match snapshot.task? occurrence with
      | none => false
      | some task =>
          !settling && !task.groups.any (fun owner => published.contains owner.ref)
  {
    snapshot with
      groupNodes :=
        snapshot.groupNodes.filterMap
          (fun node =>
            if published.contains node.group.node.ref then
              none
            else
              some { node with tasks := node.tasks.filter pending })
  }

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
