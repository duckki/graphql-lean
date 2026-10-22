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

/-- A live group record survives startup unless startup records its ref as cancelled. -/
theorem State.startNewWork_group_present_or_cancelled (queue : State) (released : NewWork)
    (available : List (Occurrence × Nat) := []) {owner : GroupNode}
    (present : owner ∈ queue.groupNodes)
    : owner ∈ (queue.startNewWork released available).1.groupNodes
      ∨ owner.group.node.ref
        ∈ (queue.startNewWork released available).1.cancelledGroups := by
  have group (current : State) (ref : NodeRef) (member : owner ∈ current.groupNodes)
      : owner ∈ (current.startGroup ref available).1.groupNodes
        ∨ owner.group.node.ref
          ∈ (current.startGroup ref available).1.cancelledGroups := by
    have cached : owner ∈ (current.cacheTaskFailures available).groupNodes := by
      rwa [State.cacheTaskFailures_groupNodes]
    unfold State.startGroup
    dsimp only
    split
    · exact .inl cached
    · rename_i node found
      split
      · have unchanged (tasks : List Occurrence) (state : State)
            : (tasks.foldl (fun state task => state.startTask task available) state).groupNodes
              = state.groupNodes := by
          induction tasks generalizing state with
          | nil => rfl
          | cons task rest ih => rw [List.foldl_cons, ih, State.startTask_groupNodes]
        exact .inl (by rwa [unchanged])
      · let removed := State.removeGroup.collect
          ((current.cacheTaskFailures available).groupNodes.length + 1)
          (current.cacheTaskFailures available) [node.group.node.ref] []
        by_cases cancelled : owner.group.node.ref ∈ removed
        · exact .inr (List.mem_append_right _ cancelled)
        · exact .inl (List.mem_filter.mpr ⟨cached, by
            change (!removed.contains owner.group.node.ref) = true
            simp [cancelled]⟩)
  have groups (refs : NodeRefs) (acc : State × List GroupFailureEvent)
      (prior : owner ∈ acc.1.groupNodes ∨ owner.group.node.ref ∈ acc.1.cancelledGroups)
      : owner ∈ (refs.foldl (fun (current, failures) ref =>
          let (next, queued) := current.startGroup ref available
          (next, failures ++ queued)) acc).1.groupNodes
        ∨ owner.group.node.ref ∈ (refs.foldl (fun (current, failures) ref =>
          let (next, queued) := current.startGroup ref available
          (next, failures ++ queued)) acc).1.cancelledGroups := by
    induction refs generalizing acc with
    | nil => exact prior
    | cons ref rest ih =>
        apply ih
        rcases prior with live | cancelled
        · exact group acc.1 ref live
        · exact .inr ((acc.1.startGroup_cancelledGroups_prefix ref available).subset cancelled)
  have streams (refs : NodeRefs) (current : State)
      (prior : owner ∈ current.groupNodes ∨ owner.group.node.ref ∈ current.cancelledGroups)
      : owner ∈ (refs.foldl State.startStream current).groupNodes
        ∨ owner.group.node.ref ∈ (refs.foldl State.startStream current).cancelledGroups := by
    induction refs generalizing current with
    | nil => exact prior
    | cons ref rest ih =>
        apply ih
        unfold State.startStream
        split <;> exact prior
  unfold State.startNewWork
  exact streams _ _ (groups _ _ (.inl present))

/-- Startup preserves every buffered owner that remains uncancelled.
Witness: a removed record is recorded in cancellation history; a surviving contributor
retains the exact task lookup when its own rejection is absent from the snapshot.
-/
theorem State.startNewWork_storedOwnersConserved (queue : State) (released : NewWork)
    (available : List (Occurrence × Nat) := [])
    (clean
      : queue.StoredValuesSatisfy
          (fun occurrence _ =>
            ∀ errors, (occurrence, errors) ∉ available) := by
        intro node member value stored errors impossible; cases impossible)
    : queue.StoredOwnersConserved [] (queue.startNewWork released available).1 := by
  intro occurrence node value found stored ref contributes present uncancelled
  obtain ⟨owner, live, same⟩ := List.mem_map.mp present
  have survives : owner ∈ (queue.startNewWork released available).1.groupNodes := by
    rcases queue.startNewWork_group_present_or_cancelled released available live with
      kept | cancelled
    · exact kept
    · exact False.elim (uncancelled (same ▸ cancelled))
  obtain ⟨contributor, contributes, refEq⟩ := List.mem_map.mp contributes
  have own := clean node (State.taskNode?_some found).1 value stored
  rw [(State.taskNode?_some found).2] at own
  exact Or.inr
    ⟨
      State.startNewWork_lookup_existing found released available own contributes
        survives (same.trans refEq.symm),
      List.mem_map.mpr ⟨owner, survives, same⟩
    ⟩

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

/-- Task rejection only appends cancellation markers while visiting active owners. -/
theorem State.taskFailure_cancelledGroups_mono (queue : State) (occurrence : Occurrence)
    (errors : Nat)
    : queue.cancelledGroups.Subset
        (queue.taskFailure occurrence errors).1.cancelledGroups := by
  cases found : queue.taskNode? occurrence with
  | none =>
      simp only [State.taskFailure, found]
      exact fun _ member => member
  | some task =>
      rw [queue.taskFailure_eq occurrence errors task found]
      exact failureGroupFold_preserves
        (fun current => queue.cancelledGroups.Subset current.cancelledGroups)
        (fun _ _ prior => prior.trans (List.subset_append_left _ _)) errors task.task.groups _
        (List.Subset.refl _)

/-- Rejection replay conserves every buffered owner that is not cancelled by that replay.
Witness: the selected task already has that rejection, so replacement preserves first
lookups; composition of the actual owner removals retains the same occurrence and ref.
-/
theorem State.taskFailure_replay_storedOwnersConserved {queue : State}
    {group occurrence errors}
    (replayed : queue.rejectedTask? group = some (occurrence, errors))
    : queue.StoredOwnersConserved [] (queue.taskFailure occurrence errors).1 := by
  obtain ⟨_, task, found, rejected⟩ := State.rejectedTask?_sound replayed
  let stored := queue.putTaskNode { task with rejection := some errors }
  have initial : queue.StoredOwnersConserved [] stored := by
    intro other node value lookup valueEq ref contributes present uncancelled
    have unchanged : stored.taskNode? other = some node := by
      have identical : { task with rejection := some errors } = task := by rw [← rejected]
      by_cases equal : occurrence = other
      · subst other
        have taskEq := Option.some.inj (found.symm.trans lookup)
        change (queue.putTaskNode _).taskNode? occurrence = some node
        rw [identical, taskEq]
        exact State.putTaskNode_lookup_same lookup node (State.taskNode?_some lookup).2
      · exact State.putTaskNode_lookup_other lookup _ (by
          simpa only [(State.taskNode?_some found).2] using equal)
    exact Or.inr ⟨unchanged, present⟩
  rw [queue.taskFailure_eq occurrence errors task found]
  apply failureGroupFold_preserves (fun current => queue.StoredOwnersConserved [] current)
    (fun current ref prior => by
      simpa only [List.nil_append] using prior.append
        (current.removeGroup_storedOwnersConserved ref) (List.subset_append_left _ _))
  exact initial

/-- A drain never forgets a cancelled group ref.
Witness: successful flushing preserves cancellation history, and startup removal can
extend it. The induction follows the actual finite drain budget.
-/
theorem State.drainReadyGroups_go_cancelledGroups_subset (fuel : Nat) (queue : State)
    (available : List (Occurrence × Nat) := [])
    : queue.cancelledGroups.Subset
        (State.drainReadyGroups.go available fuel queue).1.cancelledGroups := by
  induction fuel generalizing queue with
  | zero => exact List.Subset.refl _
  | succ fuel ih =>
      unfold State.drainReadyGroups.go
      dsimp only
      split
      · exact List.Subset.refl _
      · rename_i group selected
        intro ref member
        apply ih _
        apply State.startNewWork_cancelledGroups_subset _ _ available
        rwa [State.finishGroupSuccess_cancelledGroups]

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
