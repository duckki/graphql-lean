import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StoredValueRetention
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.PromotionPaths

/-! Mixed recursive draining cannot lose a buffered value with a surviving contributor. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Every surviving live record was present before each bounded drain prefix
-----------------------------------------------------------------------------------------

/-- A bounded drain never creates live group records or changes their child edges.
Witness: induction over actual successful/failing iterations; promotion only activates
existing records. This holds without generated metadata or a sufficient-budget premise.
-/
theorem State.drainReadyGroups_go_groupEdgesFrom (fuel : Nat) (queue : State)
    : (State.drainReadyGroups.go fuel queue).1.GroupEdgesFrom queue := by
  induction fuel generalizing queue with
  | zero => exact .refl queue
  | succ fuel ih =>
      unfold State.drainReadyGroups.go
      dsimp only
      split
      · exact .refl queue
      · rename_i group selected
        cases cached : group.failure with
        | none =>
            dsimp only
            apply (ih _).trans
            intro key node found
            rw [State.groupNode?, (State.startNewWork_groupCore _ _).1] at found
            exact (queue.finishGroupSuccess_descendants group).1 key node found
        | some errors =>
            dsimp only
            apply (ih _).trans
            intro key node found
            exact queue.filterKeys_groupEdgesFrom
              (fun key => !(State.removeGroup.collect (queue.groupNodes.length + 1)
                queue [group.group.node.key] []).contains key)
              key node found

-----------------------------------------------------------------------------------------
-- One occurrence-labelled ledger covers successful flushes and failed cleanup together
-----------------------------------------------------------------------------------------

/-- Splitting a drain budget retains the exact intermediate queue and output order.
Witness: induction on the first budget; an exhausted ready set stays exhausted, while a
real closure contributes its output before both remaining segments. Thus a bounded drain
used below is an actual execution prefix, not a separately chosen trace.
-/
theorem State.drainReadyGroups_go_add (first rest : Nat) (queue : State)
    : State.drainReadyGroups.go (first + rest) queue
      = let before := State.drainReadyGroups.go first queue
        let after := State.drainReadyGroups.go rest before.1
        (after.1, before.2 ++ after.2) := by
  induction first generalizing queue with
  | zero => simp [State.drainReadyGroups.go]
  | succ first ih =>
      simp only [Nat.succ_add, State.drainReadyGroups.go]
      split
      · rename_i stopped
        cases rest <;> simp only [State.drainReadyGroups.go, stopped, List.nil_append]
      · rename_i group selected
        cases cached : group.failure <;> dsimp only <;>
          simp only [ih, List.append_assoc]

/-- Every stored value with a contributor still live after a drain prefix is published or
retained exactly. Witness: successful flushes extend the same publication inventory;
failed cleanup preserves the task through its surviving owner, and activation preserves
the lookup. The endpoint owner is an internal liveness condition, not a cancellation
certificate for tasks whose owners are all absent.
-/
theorem State.PublicationInventory.drainReadyGroups_go_conserves {queue : State}
    {property published} (inventory : queue.PublicationInventory property published)
    (fuel : Nat)
    : ∃ added : List ObjectPublication,
        added.map Prod.snd
          = (State.drainReadyGroups.go fuel queue).2.flatMap WorkQueueEvent.objectValues
        ∧ (State.drainReadyGroups.go fuel queue).1.PublicationInventory property
            (published ++ added)
        ∧ (∀ occurrence node value,
            queue.taskNode? occurrence = some node
            → node.value = some value
            → (∃ contributor ∈ node.task.groups,
                ∃ owner,
                  (State.drainReadyGroups.go fuel queue).1.groupNode? contributor.key
                  = some owner)
            → (occurrence, value) ∈ added
              ∨ (State.drainReadyGroups.go fuel queue).1.taskNode? occurrence
                = some node) := by
  induction fuel generalizing queue published with
  | zero =>
      exact ⟨
        [],
        rfl,
        by simpa only [State.drainReadyGroups.go, List.append_nil] using inventory,
        fun _ _ _ found _ _ => Or.inr found
      ⟩
  | succ fuel ih =>
      unfold State.drainReadyGroups.go
      dsimp only
      split
      · exact ⟨[], rfl, by simpa using inventory, fun _ _ _ found _ _ => Or.inr found⟩
      · rename_i group selected
        cases cached : group.failure with
        | none =>
            dsimp only
            obtain ⟨first, before, output, firstValues, flushed, conserved⟩ :=
              inventory.finishGroupSuccess_conserves group
            have activated := State.PublicationInventory.mk flushed.unique flushed.provenance
              (flushed.stored.startNewWork (queue.finishGroupSuccess group).2.2)
            obtain ⟨later, laterValues, final, laterConserved⟩ := ih activated
            refine ⟨first ++ later, ?_, ?_, ?_⟩
            · simp only [List.map_append, List.flatMap_append, output,
                List.flatMap_singleton, WorkQueueEvent.objectValues, List.append_nil,
                firstValues, laterValues]
            · simpa only [List.append_assoc] using final
            · intro occurrence node value found stored live
              rcases conserved occurrence node value found stored with earlier | retained
              · exact Or.inl (List.mem_append_left _ earlier)
              · rcases laterConserved occurrence node value
                  (State.startNewWork_lookup_existing retained _) stored live with now | still
                · exact Or.inl (List.mem_append_right _ now)
                · exact Or.inr still
        | some errors =>
            dsimp only
            have cleaned := State.PublicationInventory.mk inventory.unique inventory.provenance
              (inventory.stored.removeGroup group.group.node.key)
            obtain ⟨added, values, final, conserved⟩ := ih cleaned
            refine ⟨added, ?_, final, ?_⟩
            · simpa only [State.finishGroupFailure, List.flatMap_append,
                List.flatMap_singleton, WorkQueueEvent.objectValues, List.nil_append] using values
            · intro occurrence node value found stored live
              obtain ⟨contributor, contributes, owner, finalOwner⟩ := live
              obtain ⟨survivor, survives, _⟩ :=
                State.drainReadyGroups_go_groupEdgesFrom fuel _ _ _ finalOwner
              have kept := State.removeGroup_lookup_survivingOwner found group.group.node.key
                contributes (List.mem_of_find?_eq_some survives) (State.groupNode?_key survives)
              exact conserved occurrence node value kept stored
                ⟨contributor, contributes, owner, finalOwner⟩

/-- Full release-time draining retains or publishes every value with a surviving owner.
Witness: specialize bounded conservation to the implementation's live-node budget.
Cached failures and recursively promoted successes use one compatible publication ledger.
-/
theorem State.PublicationInventory.drainReadyGroups_conserves {queue : State}
    {property published} (inventory : queue.PublicationInventory property published)
    : ∃ added : List ObjectPublication,
        added.map Prod.snd = queue.drainReadyGroups.2.flatMap WorkQueueEvent.objectValues
        ∧ queue.drainReadyGroups.1.PublicationInventory property (published ++ added)
        ∧ (∀ occurrence node value,
            queue.taskNode? occurrence = some node
            → node.value = some value
            → (∃ contributor ∈ node.task.groups,
                ∃ owner, queue.drainReadyGroups.1.groupNode? contributor.key = some owner)
            → (occurrence, value) ∈ added
              ∨ queue.drainReadyGroups.1.taskNode? occurrence = some node) :=
  inventory.drainReadyGroups_go_conserves queue.groupNodes.length

-----------------------------------------------------------------------------------------
-- Values present before a mixed drain prefix are covered before a later live-owner close
-----------------------------------------------------------------------------------------

/-- A stored contributor publishes strictly before a later successful closure, even when
the preceding bounded drain mixes failures and successes. Witness: the closing owner's
live lookup protects the value through that prefix; active membership then supplies the
final flush. Both stages extend one occurrence-labelled inventory. Replay must establish
the actual closing boundary and its active links; no absent-task cancellation is inferred.
-/
theorem State.PublicationInventory.drainPrefix_finishGroupSuccess_contributors
    {queue : State} {property published}
    (inventory : queue.PublicationInventory property published)
    (fuel : Nat) (group : GroupNode)
    (found
      : (State.drainReadyGroups.go fuel queue).1.groupNode? group.group.node.key
        = some group)
    (active : group.group.node.key ∈ (State.drainReadyGroups.go fuel queue).1.rootGroups)
    (links : (State.drainReadyGroups.go fuel queue).1.ActiveTaskLinks)
    : let drained := State.drainReadyGroups.go fuel queue
      let closed := drained.1.finishGroupSuccess group
      ∃ (added : List ObjectPublication) (before : List WorkQueueEvent),
        drained.2 ++ closed.2.1
          = before
            ++ [.groupSuccess group.group.node closed.2.2.newGroups closed.2.2.newStreams]
        ∧ added.map Prod.snd = before.flatMap WorkQueueEvent.objectValues
        ∧ closed.1.PublicationInventory property (published ++ added)
        ∧ (∀ occurrence node value,
            queue.taskNode? occurrence = some node
            → node.value = some value
            → group.group.node.key ∈ node.task.groups.map Execution.DeliveryNode.key
            → (occurrence, value) ∈ added) := by
  dsimp only
  obtain ⟨first, firstValues, advanced, conserved⟩ :=
    inventory.drainReadyGroups_go_conserves fuel
  obtain ⟨last, closeBefore, closeOutput, lastValues, final, covered⟩ :=
    advanced.finishGroupSuccess_contributors links group (List.mem_of_find?_eq_some found) active
  refine ⟨first ++ last, (State.drainReadyGroups.go fuel queue).2 ++ closeBefore, ?_, ?_, ?_, ?_⟩
  · rw [closeOutput, List.append_assoc]
  · simp only [List.map_append, List.flatMap_append, firstValues, lastValues]
  · simpa only [List.append_assoc] using final
  · intro occurrence node value lookup stored contributes
    obtain ⟨contributor, member, same⟩ := List.mem_map.mp contributes
    have live : ∃ contributor ∈ node.task.groups, ∃ owner,
        (State.drainReadyGroups.go fuel queue).1.groupNode? contributor.key = some owner :=
      ⟨contributor, member, group, same.symm ▸ found⟩
    rcases conserved occurrence node value lookup stored live with earlier | retained
    · exact List.mem_append_left _ earlier
    · exact List.mem_append_right _
        (covered occurrence node value retained stored (List.mem_map.mpr ⟨_, member, same⟩))

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
