import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.HostProtocol
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupPublication

/-! Safety of the actual fused removal, without an output scan or registration observer.
Every claim below uses the same real task-fold and shrinking-walk endpoint. A held source
is either still linked there or present in the returned cleanup identities; this is not
native acquisition completeness or asynchronous cleanup settlement.
-/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
open WorkQueueSemantics (NodeRefs Occurrence)
open ReferenceWorkQueue (TaskNode GroupNode)

-----------------------------------------------------------------------------------------
-- Name the literal task step inside the public walk for proof induction
-----------------------------------------------------------------------------------------

private def removalTaskStep (acc : State × List CleanupTarget) (occurrence : Occurrence)
    : State × List CleanupTarget :=
  match acc.1.queue.task? occurrence with
  | none => acc
  | some task =>
      if task.groups.all (fun owner => (acc.1.queue.groupNode? owner.ref).isNone) then
        (
          { acc.1 with queue := acc.1.queue.removeTask occurrence },
          uniqueCleanupTargets (acc.2 ++ acc.1.cancelTask occurrence)
        )
      else
        acc

private theorem removalTaskStep_keepsTargets (acc : State × List CleanupTarget)
    (occurrence : Occurrence)
    : acc.2.Subset (removalTaskStep acc occurrence).2 := by
  unfold removalTaskStep
  split
  · exact List.Subset.refl _
  · split
    · intro target member
      rw [mem_uniqueCleanupTargets]
      exact List.mem_append_left _ member
    · exact List.Subset.refl _

private theorem removalTaskStep_nodup (acc : State × List CleanupTarget)
    (occurrence : Occurrence) (unique : acc.2.Nodup)
    : (removalTaskStep acc occurrence).2.Nodup := by
  unfold removalTaskStep
  split
  · exact unique
  · split
    · exact uniqueCleanupTargets_nodup _
    · exact unique

private theorem removalTaskStep_heldSource (acc : State × List CleanupTarget)
    (chosen : Occurrence) {occurrence node key}
    (found : acc.1.queue.taskNode? occurrence = some node)
    (held : key ∈ node.childStreams)
    : (removalTaskStep acc chosen).1.queue.taskNode? occurrence = some node
      ∨ .stream key ∈ (removalTaskStep acc chosen).2 := by
  unfold removalTaskStep
  split
  · exact Or.inl found
  · split
    · by_cases same : occurrence = chosen
      · subst chosen
        apply Or.inr
        rw [mem_uniqueCleanupTargets]
        apply List.mem_append_right
        simp only [State.cancelTask, found, Option.toList_some, List.flatMap_cons,
          List.flatMap_nil, List.append_nil]
        exact List.mem_append_right _ (List.mem_map.mpr ⟨key, held, rfl⟩)
      · exact Or.inl ((ReferenceWorkQueue.State.removeTask_lookup_other _ same).trans found)
    · exact Or.inl found

private theorem removalTaskFold_keepsTargets (tasks : List Occurrence)
    (acc : State × List CleanupTarget)
    : acc.2.Subset (tasks.foldl removalTaskStep acc).2 := by
  induction tasks generalizing acc with
  | nil => exact List.Subset.refl _
  | cons occurrence rest ih =>
      exact (removalTaskStep_keepsTargets acc occurrence).trans (ih _)

private theorem removalTaskFold_nodup (tasks : List Occurrence)
    (acc : State × List CleanupTarget) (unique : acc.2.Nodup)
    : (tasks.foldl removalTaskStep acc).2.Nodup := by
  induction tasks generalizing acc with
  | nil => exact unique
  | cons occurrence rest ih => exact ih _ (removalTaskStep_nodup acc occurrence unique)

private theorem removalTaskFold_heldSource (tasks : List Occurrence)
    (acc : State × List CleanupTarget) {occurrence node key}
    (found : acc.1.queue.taskNode? occurrence = some node)
    (held : key ∈ node.childStreams)
    : (tasks.foldl removalTaskStep acc).1.queue.taskNode? occurrence = some node
      ∨ .stream key ∈ (tasks.foldl removalTaskStep acc).2 := by
  induction tasks generalizing acc with
  | nil => exact Or.inl found
  | cons chosen rest ih =>
      rcases removalTaskStep_heldSource acc chosen found held with kept | requested
      · exact ih _ kept
      · exact Or.inr (removalTaskFold_keepsTargets rest _ requested)

-----------------------------------------------------------------------------------------
-- Shrinking-walk safety uses the actual returned state and cumulative targets
-----------------------------------------------------------------------------------------

private def withoutGroup (state : State) (key : Nat) : State :=
  {
    state with
      queue :=
        {
          state.queue with
            groupNodes :=
              state.queue.groupNodes.filter (fun node => node.group.node.ref != key)
            rootGroups := state.queue.rootGroups.filter (· != key)
        }
  }

/-- At every finite walker budget, earlier requests survive, uniqueness is preserved, and
no held source loses its exact record without a cleanup target. This includes raw cycles,
stale links and duplicate memberships; exhaustion does not certify subtree completeness.
-/
theorem removeGroup_walk_safety (fuel : Nat) (state : State) (pending removed : NodeRefs)
    (targets : List CleanupTarget)
    : let final := State.removeGroup.walk fuel state pending removed targets
      targets.Subset final.2.2
      ∧ (targets.Nodup → final.2.2.Nodup)
      ∧ ∀ occurrence node key,
          state.queue.taskNode? occurrence = some node
          → key ∈ node.childStreams
          → final.1.queue.taskNode? occurrence = some node ∨ .stream key ∈ final.2.2 := by
  induction fuel generalizing state pending removed targets with
  | zero =>
      simp only [State.removeGroup.walk]
      exact ⟨List.Subset.refl _, fun unique => unique, fun _ _ _ found _ => Or.inl found⟩
  | succ fuel ih =>
      induction pending generalizing state removed targets with
      | nil =>
          simp only [State.removeGroup.walk]
          exact ⟨List.Subset.refl _, fun unique => unique, fun _ _ _ found _ => Or.inl found⟩
      | cons key rest tailIH =>
          cases found : state.queue.groupNode? key with
          | none =>
              simpa only [State.removeGroup.walk, found] using tailIH state removed targets
          | some group =>
              rw [State.removeGroup.walk, found]
              let folded := group.tasks.foldl removalTaskStep (withoutGroup state key, targets)
              have next := ih folded.1 (group.childGroups ++ rest) (key :: removed) folded.2
              change targets.Subset (State.removeGroup.walk fuel folded.1
                (group.childGroups ++ rest) (key :: removed) folded.2).2.2 ∧ _
              refine ⟨(removalTaskFold_keepsTargets group.tasks _).trans next.1,
                fun unique => next.2.1 (removalTaskFold_nodup group.tasks _ unique), ?_⟩
              intro occurrence node heldKey lookup held
              have prior : (withoutGroup state key).queue.taskNode? occurrence = some node := lookup
              rcases removalTaskFold_heldSource group.tasks
                (withoutGroup state key, targets) prior held with kept | requested
              · exact next.2.2 occurrence node heldKey kept held
              · exact Or.inr (next.1 requested)

/-- Exact actual-removal safety target. It supplies no native inventory or final-owner
assumption: looked-up held records define the domain, and the real reduction supplies both
the retained record and cleanup alternative.
-/
def FusedRemovalSafety : Prop :=
  ∀ (state : State) (root : Nat) (targets : List CleanupTarget),
    let final := state.removeGroup root targets
    targets.Subset final.2
    ∧ (targets.Nodup → final.2.Nodup)
    ∧ ∀ occurrence node key,
        state.queue.taskNode? occurrence = some node
        → key ∈ node.childStreams
        → final.1.queue.taskNode? occurrence = some node ∨ .stream key ∈ final.2

/-- Cancelled-key bookkeeping changes no lookup or cleanup identity, so the walker fact
lifts to the exact public wrapper without any generated-work premise.
-/
theorem FusedRemovalSafety_holds : FusedRemovalSafety := by
  intro state root targets
  exact removeGroup_walk_safety (state.queue.groupNodes.length + 1) state [root] [] targets

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
