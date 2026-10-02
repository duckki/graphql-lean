import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.IntegrationPaths
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ForestPathPreservation
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.PrunedFrontierUniqueness

/-! Fresh work integration and taskless pruning cannot disconnect earlier live work. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Pruning outside a target preserves every existing path to that target
-----------------------------------------------------------------------------------------

/-- Every live descendant path ends at an existing record.
Witness: follow its child constructors to the final successful lookup.
-/
theorem State.LiveDescendant.target_present {queue : State} {root target}
    (path : queue.LiveDescendant root target)
    : ∃ node, queue.groupNode? target = some node := by
  induction path with
  | self found => exact ⟨_, found⟩
  | child found linked below ih => exact ih

/-- Pruning unrelated subtrees retains a complete path to the protected target.
Witness: a removed candidate cannot lie on that path. Its promoted children remain
unrelated by prepending the candidate's edge; key filtering creates no new path.
This frame property needs neither a sufficient fuel proof nor an incoming-free frontier.
-/
theorem State.LiveDescendant.pruneEmptyGroups_outside {queue : State} {root target}
    (path : queue.LiveDescendant root target) (groups : List Execution.DeliveryNode)
    (outside : ∀ group ∈ groups, ¬queue.LiveDescendant group.key target)
    : (queue.pruneEmptyGroups groups).1.LiveDescendant root target := by
  have loop (fuel : Nat) (current : State) (remaining kept : List Execution.DeliveryNode)
      (path : current.LiveDescendant root target)
      (outside : ∀ group ∈ remaining, ¬current.LiveDescendant group.key target)
      : (State.pruneEmptyGroups.go fuel current remaining kept).1.LiveDescendant root target := by
    induction fuel generalizing current remaining kept with
    | zero => exact path
    | succ fuel ih =>
        cases remaining with
        | nil => exact path
        | cons group rest =>
            unfold State.pruneEmptyGroups.go
            split
            · exact ih _ _ _ path (fun child member =>
                outside child (List.mem_cons_of_mem _ member))
            · rename_i node found
              split
              · apply ih _ _ _ (path.filter_outside (outside group List.mem_cons_self))
                intro child member reaches
                have earlier :=
                  (current.filterKeys_groupEdgesFrom (fun key => key != group.key)).liveDescendant
                    reaches
                rcases List.mem_append.mp member with promoted | prior
                · exact outside group List.mem_cons_self
                    (.child found (State.childDescriptors_member promoted).1 earlier)
                · exact outside child (List.mem_cons_of_mem _ prior) earlier
              · exact ih _ _ _ path (fun child member =>
                  outside child (List.mem_cons_of_mem _ member))
  exact loop _ queue groups [] path outside

-----------------------------------------------------------------------------------------
-- Fresh registration and its initial pruning preserve old root coverage
-----------------------------------------------------------------------------------------

/-- Pruning newly integrated work preserves every pre-integration live group path.
Witness: integration preserves the path, and a fresh candidate cannot reach its old
registered target. The unrelated-subtree frame then applies even to taskless promotion.
-/
theorem State.LiveDescendant.pruneIntegratedWork {queue : State} {root target}
    (path : queue.LiveDescendant root target) (unique : queue.GroupKeysUnique)
    (registered : queue.LiveGroupsRegistered) (work : Work)
    (parentTask : Option Occurrence := none)
    : let integrated := queue.maybeIntegrateWork work parentTask
      (integrated.1.pruneEmptyGroups integrated.2.newGroups).1.LiveDescendant root
        target := by
  intro integrated
  obtain ⟨node, found⟩ := path.target_present
  have old : target ∈ queue.registeredGroups :=
    State.groupNode?_key found ▸ registered node (List.mem_of_find?_eq_some found)
  apply (path.maybeIntegrateWork unique work parentTask).pruneEmptyGroups_outside
  intro candidate member reaches
  obtain ⟨_, _, _, _, fresh, _⟩ := queue.addGroups_newGroup_candidate work.groups member
  exact ((queue.maybeIntegrateWork_freshChildLinks registered work parentTask).descendant
    reaches fresh) old

/-- Stream-item integration preserves all earlier live group paths through activation.
Witness: fresh integration/pruning preserves the path and starting the new roots does
not change the live group map. The item may carry arbitrary finite work.
-/
theorem State.LiveDescendant.integrateStreamItem {queue : State} {root target}
    (path : queue.LiveDescendant root target) (unique : queue.GroupKeysUnique)
    (registered : queue.LiveGroupsRegistered) (item : StreamItem)
    : (queue.integrateStreamItem item).LiveDescendant root target := by
  let integrated := queue.maybeIntegrateWork item.work
  let pruned := integrated.1.pruneEmptyGroups integrated.2.newGroups
  let released := { integrated.2 with newGroups := pruned.2 }
  exact (path.pruneIntegratedWork unique registered item.work).of_groupNodes_eq
    (pruned.1.startNewWork_groupCore released).1

/-- An item carrying new work cannot strand a previously root-covered group.
Witness: the previous root and its entire child path survive fresh integration and pruning;
activation retains old roots while appending the new notice frontier.
-/
theorem State.integrateStreamItem_old_root_coverage {queue : State} {target}
    (unique : queue.GroupKeysUnique) (registered : queue.LiveGroupsRegistered)
    (item : StreamItem)
    (covered : ∃ root ∈ queue.rootGroups, queue.LiveDescendant root target)
    : ∃ root ∈ (queue.integrateStreamItem item).rootGroups,
        (queue.integrateStreamItem item).LiveDescendant root target := by
  obtain ⟨root, member, path⟩ := covered
  refine ⟨root, ?_, path.integrateStreamItem unique registered item⟩
  unfold State.integrateStreamItem
  rw [(State.startNewWork_groupCore _ _).2.2, State.pruneEmptyGroups_rootGroups,
    State.maybeIntegrateWork_rootGroups]
  exact List.mem_append_left _ member

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
