import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.BufferedOwnerRetention
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.CancellationPreservation

/-! A contributor retires only after its buffered data publishes or that ref is cancelled. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Track one initially live owner along with the exact buffered value
-----------------------------------------------------------------------------------------

/-- A buffered task's initially live owner either releases its value or remains live.
`published` fixes occurrence/value pairs emitted between `queue` and `next`. NodeRefs recorded
as cancelled in `next` are excluded: cancellation may discard their unpublished data.
The retained branch preserves the exact task node as well as the contributor's presence.
-/
def State.StoredOwnersConserved (queue : State) (published : List ObjectPublication)
    (next : State)
    : Prop :=
  ∀ occurrence node value,
    queue.taskNode? occurrence = some node
    → node.value = some value
    → ∀ ref ∈ node.task.groups.map Execution.DeliveryNode.ref,
        ref ∈ queue.groupNodes.map (fun owner => owner.group.node.ref)
        → ref ∉ next.cancelledGroups
        → (occurrence, value) ∈ published
          ∨ (next.taskNode? occurrence = some node
              ∧ ref ∈ next.groupNodes.map (fun owner => owner.group.node.ref))

/-- An unchanged queue retains both value and owner. Witness: the supplied lookups. -/
theorem State.StoredOwnersConserved.refl (queue : State)
    : queue.StoredOwnersConserved [] queue := by
  intro occurrence node value found stored ref contributes present uncancelled
  exact Or.inr ⟨found, present⟩

/-- Consecutive certificates keep the same buffered occurrence and contributor ref.
Witness: published labels persist under concatenation; otherwise the first retained
lookup and owner feed the second certificate. Cancellation history grows monotonically.
-/
theorem State.StoredOwnersConserved.append {queue middle next : State} {first later}
    (before : queue.StoredOwnersConserved first middle)
    (after : middle.StoredOwnersConserved later next)
    (cancelled : middle.cancelledGroups.Subset next.cancelledGroups)
    : queue.StoredOwnersConserved (first ++ later) next := by
  intro occurrence node value found stored ref contributes present uncancelled
  rcases before occurrence node value found stored ref contributes present
      (fun member => uncancelled (cancelled member)) with emitted | retained
  · exact Or.inl (List.mem_append_left _ emitted)
  · rcases after occurrence node value retained.1 stored ref contributes retained.2
        uncancelled with emitted | retained
    · exact Or.inl (List.mem_append_right _ emitted)
    · exact Or.inr retained

/-- A group-record update preserves every buffered owner ref and task lookup.
Witness: record replacement keeps its ref and never changes the task map.
-/
theorem State.putGroupNode_storedOwnersConserved (queue : State) (updated : GroupNode)
    : queue.StoredOwnersConserved [] (queue.putGroupNode updated) := by
  intro occurrence node value found stored ref contributes present uncancelled
  refine Or.inr ⟨found, ?_⟩
  rwa [State.putGroupNode_refs]

-----------------------------------------------------------------------------------------
-- Activation and pruning never silently drop a buffered owner's record
-----------------------------------------------------------------------------------------

/-- Activation preserves all existing buffered owners and values.
Witness: exact lookup preservation and unchanged group records; it only starts new work.
-/
theorem State.startNewWork_storedOwnersConserved (queue : State) (released : NewWork)
    : queue.StoredOwnersConserved [] (queue.startNewWork released) := by
  intro occurrence node value found stored ref contributes present uncancelled
  refine Or.inr ⟨State.startNewWork_lookup_existing found released, ?_⟩
  rwa [(State.startNewWork_groupCore queue released).1]

/-- Empty-shell pruning preserves every live buffered contributor.
Witness: pruning leaves task lookups unchanged, while buffered membership contradicts
the empty-task test for any shell with the contributor's ref.
-/
theorem State.pruneEmptyGroups_storedOwnersConserved {queue : State}
    (links : queue.StoredTaskLinks) (groups : List Execution.DeliveryNode)
    : queue.StoredOwnersConserved [] (queue.pruneEmptyGroups groups).1 := by
  intro occurrence node value found stored ref contributes present uncancelled
  refine Or.inr ⟨?_, ?_⟩
  · simpa only [State.taskNode?, State.pruneEmptyGroups_taskNodes] using found
  · exact State.pruneEmptyGroups_bufferedOwner_present links
      (State.taskNode?_some found).1 (by simp [stored]) contributes present groups

-----------------------------------------------------------------------------------------
-- Failed cleanup records a removed owner; successful cleanup publishes its value
-----------------------------------------------------------------------------------------

/-- Failed cleanup retains a buffered owner unless it records that ref as cancelled.
Witness: the removed-ref list is appended to cancellation history. An uncancelled ref
passes the group filter, and its surviving record preserves the exact task lookup.
-/
theorem State.removeGroup_storedOwnersConserved (queue : State) (removed : Nat)
    : queue.StoredOwnersConserved [] (queue.removeGroup removed) := by
  intro occurrence node value found stored ref contributes present uncancelled
  obtain ⟨owner, live, same⟩ := List.mem_map.mp present
  have retained : owner ∈ (queue.removeGroup removed).groupNodes := by
    apply List.mem_filter.mpr
    refine ⟨live, ?_⟩
    have absent : ref ∉ State.removeGroup.collect (queue.groupNodes.length + 1)
        queue [removed] [] := by
      intro member
      exact uncancelled (List.mem_append_right _ member)
    simpa [same] using absent
  obtain ⟨contributor, member, refEq⟩ := List.mem_map.mp contributes
  exact Or.inr ⟨State.removeGroup_lookup_survivingOwner found removed member retained
      (same.trans refEq.symm), List.mem_map.mpr ⟨owner, retained, same⟩⟩

/-- A flush's existing value-conservation witness also conserves buffered live owners.
Witness: a retained exact lookup invokes the successful-flush owner-retention theorem.
The supplied publication list is unchanged; no second existential ledger is selected.
-/
theorem State.finishGroupSuccess_storedOwnersConserved {queue : State}
    (links : queue.StoredTaskLinks) (group : GroupNode) (live : group ∈ queue.groupNodes)
    {published : List ObjectPublication}
    (conserved
      : ∀ occurrence node value,
          queue.taskNode? occurrence = some node
          → node.value = some value
          → (occurrence, value) ∈ published
            ∨ (queue.finishGroupSuccess group).1.taskNode? occurrence = some node)
    : queue.StoredOwnersConserved published (queue.finishGroupSuccess group).1 := by
  intro occurrence node value found stored ref contributes present uncancelled
  rcases conserved occurrence node value found stored with emitted | retained
  · exact Or.inl emitted
  · exact Or.inr ⟨retained, State.finishGroupSuccess_bufferedOwner_present links group live
      (State.taskNode?_some retained).1 (by simp [stored]) contributes present⟩

-----------------------------------------------------------------------------------------
-- Concrete cancellation history grows throughout the bounded mixed drain
-----------------------------------------------------------------------------------------

/-- A drain never forgets a cancelled group ref.
Witness: failed cleanup appends removed refs; successful flushing and activation leave
cancellation history unchanged. The induction follows the actual finite drain budget.
-/
theorem State.drainReadyGroups_go_cancelledGroups_subset (fuel : Nat) (queue : State)
    : queue.cancelledGroups.Subset
        (State.drainReadyGroups.go fuel queue).1.cancelledGroups := by
  induction fuel generalizing queue with
  | zero => exact List.Subset.refl _
  | succ fuel ih =>
      unfold State.drainReadyGroups.go
      dsimp only
      split
      · exact List.Subset.refl _
      · rename_i group selected
        cases cached : group.failure with
        | none =>
            dsimp only
            intro ref member
            apply ih _
            rwa [State.startNewWork_cancelledGroups, State.finishGroupSuccess_cancelledGroups]
        | some errors =>
            dsimp only
            intro ref member
            exact ih _ (List.mem_append_left _ member)

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
