import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.CompleteFailureAccounting
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ActiveLinks

/-! The finite release-time drain exhausts every ready active group. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (ExecutionGroupValue)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Every actual drain iteration consumes a live node and never creates another
-----------------------------------------------------------------------------------------

/-- Filtering out an existing member strictly decreases a finite list's length.
Witness: equality in the filter length bound would retain every original member.
-/
private theorem filter_length_lt_of_rejected {α : Type} {items : List α}
    (keep : α → Bool) {item : α} (member : item ∈ items) (rejected : keep item = false)
    : (items.filter keep).length < items.length := by
  have bound := List.length_filter_le keep items
  have different : (items.filter keep).length ≠ items.length := by
    intro equal
    have retained := List.length_filter_eq_length_iff.mp equal item member
    simp [rejected] at retained
  omega

/-- Pruning retains a subsequence of its original live nodes.
Witness: induction over the pruning budget; only node filtering changes the live map.
-/
theorem State.pruneEmptyGroups_groupNodes_sublist (queue : State)
    (groups : List Execution.DeliveryNode)
    : (queue.pruneEmptyGroups groups).1.groupNodes.Sublist queue.groupNodes := by
  have loop (fuel : Nat) (current : State) (remaining kept)
      : (State.pruneEmptyGroups.go fuel current remaining kept).1.groupNodes.Sublist
          current.groupNodes := by
    induction fuel generalizing current remaining kept with
    | zero => exact .refl _
    | succ fuel ih =>
        cases remaining with
        | nil => exact .refl _
        | cons group rest =>
            unfold State.pruneEmptyGroups.go
            split
            · exact ih _ _ _
            · split
              · exact (ih _ _ _).trans List.filter_sublist
              · exact ih _ _ _
  exact loop _ queue groups []

/-- Cancelling a live group strictly decreases the live-node count.
Witness: the removal filter excludes the selected group's key, including duplicate nodes.
No forest or source-admission assumption is required for this size decrease.
-/
theorem State.removeGroup_length_lt {queue : State} {key node}
    (found : queue.groupNode? key = some node)
    : (queue.removeGroup key).groupNodes.length < queue.groupNodes.length := by
  apply filter_length_lt_of_rejected _ (List.mem_of_find?_eq_some found)
  have absent := queue.removeGroup_ownGroupAbsent key
  have different : node ∉ (queue.removeGroup key).groupNodes := by
    intro member
    have noKey := List.find?_eq_none.mp absent node member
    simp [State.groupNode?_key found] at noKey
  apply Bool.eq_false_iff.mpr
  intro retained
  exact different (List.mem_filter.mpr ⟨List.mem_of_find?_eq_some found, retained⟩)

/-- Flushing a live group strictly decreases the live-node count before activation.
Witness: task removal preserves the key list; closing removes an existing key and pruning
only filters further. This also covers shared stored tasks and stale child links.
-/
theorem State.finishGroupSuccess_length_lt {queue : State} {group : GroupNode}
    (member : group ∈ queue.groupNodes)
    : (queue.finishGroupSuccess group).1.groupNodes.length < queue.groupNodes.length := by
  let keyOf := fun node : GroupNode => node.group.node.key
  let step (acc : State × List ExecutionGroupValue × Keys) (occurrence : Occurrence) :=
    let (current, values, streams) := acc
    match current.taskNode? occurrence with
    | none => (current, values, streams)
    | some taskNode =>
        let values := match taskNode.value with
          | none => values
          | some value => values ++ [value]
        (current.removeTask occurrence, values, streams ++ taskNode.childStreams)
  have foldKeys (tasks : List Occurrence) (acc : State × List ExecutionGroupValue × Keys)
      : (tasks.foldl step acc).1.groupNodes.map keyOf = acc.1.groupNodes.map keyOf := by
    induction tasks generalizing acc with
    | nil => rfl
    | cons task rest ih =>
        rw [List.foldl_cons, ih]
        obtain ⟨current, values, streams⟩ := acc
        dsimp only [step]
        split
        · rfl
        · simp [State.removeTask, List.map_map, keyOf]
  let flushed := (group.tasks.foldl step (queue, [], [])).1
  have keys : flushed.groupNodes.map keyOf = queue.groupNodes.map keyOf :=
    foldKeys group.tasks (queue, [], [])
  have lengths : flushed.groupNodes.length = queue.groupNodes.length := by
    simpa using congrArg List.length keys
  have included : group.group.node.key ∈ flushed.groupNodes.map keyOf := by
    rw [keys]
    exact List.mem_map_of_mem member
  obtain ⟨old, oldMember, sameKey⟩ := List.mem_map.mp included
  have shorter := filter_length_lt_of_rejected
    (fun node : GroupNode => node.group.node.key != group.group.node.key) oldMember
    (by simp [← sameKey, keyOf])
  let current : State :=
    { flushed with
      groupNodes := flushed.groupNodes.filter
        (fun node => node.group.node.key != group.group.node.key)
      rootGroups := flushed.rootGroups.filter (· != group.group.node.key) }
  have bound := (current.pruneEmptyGroups_groupNodes_sublist
    (group.childGroups.filterMap
      (fun key => (current.groupNode? key).map (fun node => node.group.node)))).length_le
  change (current.pruneEmptyGroups _).1.groupNodes.length < queue.groupNodes.length
  rw [lengths] at shorter
  exact Nat.lt_of_le_of_lt bound shorter

-----------------------------------------------------------------------------------------
-- The supplied live-node budget is sufficient for complete draining
-----------------------------------------------------------------------------------------

/-- After draining, every active group lookup is healthy and still waiting for settlements.
Witness: induction on the actual drain budget; every selected closure strictly decreases
the live-node count. Missing/stale root entries cannot consume the budget.
This is an executable normal-form fact, not host fairness or eventual source completion.
-/
theorem State.drainReadyGroups_normalForm (queue : State)
    : ∀ key ∈ queue.drainReadyGroups.1.rootGroups,
        ∀ node,
          queue.drainReadyGroups.1.groupNode? key = some node
          → node.failure = none ∧ node.pending ≠ 0 := by
  have loop (fuel : Nat) (current : State) (enough : current.groupNodes.length ≤ fuel)
      : ∀ key ∈ (State.drainReadyGroups.go fuel current).1.rootGroups, ∀ node,
          (State.drainReadyGroups.go fuel current).1.groupNode? key = some node
          → node.failure = none ∧ node.pending ≠ 0 := by
    induction fuel generalizing current with
    | zero =>
        intro key active node found
        have empty : current.groupNodes = [] := List.length_eq_zero_iff.mp (by omega)
        simp [State.drainReadyGroups.go, State.groupNode?, empty] at found
    | succ fuel ih =>
        unfold State.drainReadyGroups.go
        dsimp only
        split
        · rename_i noneReady
          intro key active node found
          have notReady := List.findSome?_eq_none_iff.mp noneReady key active
          simp [found] at notReady
          exact notReady
        · rename_i node selected
          obtain ⟨key, active, choice⟩ := List.exists_of_findSome?_eq_some selected
          cases found : current.groupNode? key with
          | none => simp [found] at choice
          | some candidate =>
              simp only [found] at choice
              change (if candidate.failure.isSome || candidate.pending == 0 then
                some candidate else none) = some node at choice
              split at choice
              · have equal := Option.some.inj choice
                subst candidate
                have member := List.mem_of_find?_eq_some found
                cases failure : node.failure with
                | none =>
                    apply ih
                    rw [(State.startNewWork_groupCore _ _).1]
                    have decrease := State.finishGroupSuccess_length_lt member
                    omega
                | some errors =>
                    apply ih
                    have nodeKey := State.groupNode?_key found
                    have decrease := State.removeGroup_length_lt found
                    change (current.removeGroup node.group.node.key).groupNodes.length ≤ fuel
                    rw [nodeKey]
                    omega
              · contradiction
  exact loop _ queue (Nat.le_refl _)

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
