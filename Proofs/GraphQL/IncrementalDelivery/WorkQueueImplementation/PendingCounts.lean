import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.MembershipInitialization

/-! Pending-count arithmetic and shared-task settlement. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- A fresh settlement removes exactly one selected occurrence from a
duplicate-free task list. This is the arithmetic step behind decrementing a
group's pending counter.
-/
private theorem filter_length_drop_unique {α : Type} [DecidableEq α]
    (tasks : List α) (occurrence : α) (selected : α → Bool)
    (unique : tasks.Nodup) (member : occurrence ∈ tasks)
    (selectedOccurrence : selected occurrence = true)
    : (tasks.filter selected).length
      = (tasks.filter (fun task => selected task && decide (task ≠ occurrence))).length
        + 1 := by
  induction tasks with
  | nil => cases member
  | cons head tail ih =>
      obtain ⟨headAbsent, tailUnique⟩ := List.nodup_cons.mp unique
      rcases List.mem_cons.mp member with atHead | inTail
      · subst head
        have sameTail : tail.filter selected =
            tail.filter (fun task => selected task && decide (task ≠ occurrence)) := by
          apply List.filter_congr
          intro task taskMember
          have different : task ≠ occurrence := by
            intro equal
            subst task
            exact headAbsent taskMember
          simp [different]
        simp [selectedOccurrence, sameTail]
      · have different : head ≠ occurrence := by
          intro equal
          subst head
          exact headAbsent inTail
        have tailCount := ih tailUnique inTail
        by_cases headSelected : selected head = true
        · simp [headSelected, different, tailCount, Nat.add_assoc]
        · simp [headSelected, different, tailCount]

/-- The derived occurrence equality test agrees with structural equality. -/
theorem occurrence_beq_iff_eq (left right : Occurrence)
    : (left == right) = true ↔ left = right := by
  cases left with
  | executionGroup first =>
      cases right with
      | executionGroup second =>
          simp only [BEq.beq, instBEqOccurrence.beq, Occurrence.executionGroup.injEq]
          simpa only [BEq.beq] using (beq_iff_eq (a := first) (b := second))
      | item _ _ => simp only [BEq.beq, instBEqOccurrence.beq, reduceCtorEq]
  | item first index =>
      cases right with
      | executionGroup _ =>
          simp only [BEq.beq, instBEqOccurrence.beq, reduceCtorEq]
      | item second other =>
          simp only [BEq.beq, instBEqOccurrence.beq, Occurrence.item.injEq]
          simp only [Bool.and_eq_true, decide_eq_true_eq]
          exact and_congr
            (by simpa only [BEq.beq] using (beq_iff_eq (a := first) (b := second)))
            Iff.rfl

/-- Proof-only pending-token count for a group task list and settled task IDs. -/
noncomputable def unsettledCount (tasks settled : List Occurrence) : Nat := by
  classical
  exact (tasks.filter (fun task => decide (task ∉ settled))).length

/-- Registering a task that has not settled adds one pending token. -/
private theorem unsettledCount_append_fresh (tasks settled : List Occurrence)
    (occurrence : Occurrence) (fresh : occurrence ∉ settled)
    : unsettledCount (tasks ++ [occurrence]) settled
      = unsettledCount tasks settled + 1 := by
  classical
  simp [unsettledCount, List.filter_append, fresh]

/-- Settling one fresh member of a duplicate-free group removes exactly one
pending token, even when other group tasks are already settled.
-/
theorem unsettledCount_settle (tasks settled : List Occurrence)
    (occurrence : Occurrence)
    (unique : tasks.Nodup) (member : occurrence ∈ tasks)
    (fresh : occurrence ∉ settled)
    : unsettledCount tasks settled
      = unsettledCount tasks (occurrence :: settled) + 1 := by
  classical
  have filtered : tasks.filter
      (fun task => decide (task ∉ settled) && decide (task ≠ occurrence))
      = tasks.filter (fun task => decide (task ∉ occurrence :: settled)) := by
    apply List.filter_congr
    intro task taskMember
    simp [List.mem_cons, not_or, Bool.and_comm]
  have selected : (decide (occurrence ∉ settled)) = true := by
    simp [fresh]
  have count := filter_length_drop_unique tasks occurrence
    (fun task => decide (task ∉ settled)) unique member selected
  simpa only [unsettledCount, filtered] using count

/-- Removing an already settled membership does not change the number of
unsettled task tokens.
-/
theorem unsettledCount_remove_settled (tasks settled : List Occurrence)
    (occurrence : Occurrence) (already : occurrence ∈ settled)
    : unsettledCount (tasks.filter (· != occurrence)) settled
      = unsettledCount tasks settled := by
  classical
  unfold unsettledCount
  rw [List.filter_filter]
  congr 1
  apply List.filter_congr
  intro task member
  by_cases same : task = occurrence
  · subst task
    simp [already]
  · have different : (task == occurrence) = false := by
      cases equal : task == occurrence with
      | false => rfl
      | true => exact False.elim (same ((occurrence_beq_iff_eq _ _).mp equal))
    simp [bne, different]

/-- Marking an occurrence absent from a group cannot change its count. -/
theorem unsettledCount_settle_absent (tasks settled : List Occurrence)
    (occurrence : Occurrence) (absent : occurrence ∉ tasks)
    : unsettledCount tasks (occurrence :: settled) = unsettledCount tasks settled := by
  classical
  unfold unsettledCount
  congr 1
  apply List.filter_congr
  intro task member
  have different : task ≠ occurrence := by
    intro equal
    subst task
    exact absent member
  simp [different]

/-- Enlarging the settled set can only decrease the number of unsettled memberships.
Witness: the larger set filters a sublist of the smaller set's remaining tokens.
-/
theorem unsettledCount_antitone (tasks : List Occurrence) {settled more : List Occurrence}
    (included : settled.Subset more)
    : unsettledCount tasks more ≤ unsettledCount tasks settled := by
  classical
  unfold unsettledCount
  have filtered : tasks.filter (fun task => decide (task ∉ more))
      = (tasks.filter (fun task => decide (task ∉ settled))).filter
        (fun task => decide (task ∉ more)) := by
    rw [List.filter_filter]
    apply List.filter_congr
    intro task member
    by_cases absent : task ∉ more
    · have absentEarlier : task ∉ settled := fun earlier => absent (included earlier)
      simp [absent, absentEarlier]
    · simp [absent]
  rw [filtered]
  exact List.length_filter_le _ _

/-- A group node's pending counter equals its as-yet-unsettled memberships. -/
def GroupNode.PendingTracks (node : GroupNode) (settled : List Occurrence) : Prop :=
  node.pending = unsettledCount node.tasks settled

/-- Fresh task registration adds one pending token and one unsettled member. -/
theorem GroupNode.PendingTracks.register
    (node : GroupNode) (settled : List Occurrence)
    (occurrence : Occurrence)
    (tracks : node.PendingTracks settled)
    (fresh : occurrence ∉ settled)
    : ({
        node with
          tasks := node.tasks ++ [occurrence], pending := node.pending + 1
      }).PendingTracks
        settled := by
  change node.pending + 1 = unsettledCount (node.tasks ++ [occurrence]) settled
  rw [tracks, unsettledCount_append_fresh node.tasks settled occurrence fresh]

/-- A fresh successful settlement decrements the exact pending count by one.
Duplicate-free membership is needed: otherwise one settlement could remove
more than one token from the abstract count.
-/
theorem GroupNode.PendingTracks.settle
    (node : GroupNode) (settled : List Occurrence)
    (occurrence : Occurrence)
    (tracks : node.PendingTracks settled)
    (unique : node.tasks.Nodup)
    (member : occurrence ∈ node.tasks)
    (fresh : occurrence ∉ settled)
    : ({ node with pending := node.pending - 1 }).PendingTracks
        (occurrence :: settled) := by
  change node.pending - 1 = unsettledCount node.tasks (occurrence :: settled)
  rw [tracks, unsettledCount_settle node.tasks settled occurrence unique member fresh]
  simp

/-- A zero pending count certifies that every remaining group membership has
already settled, even if its stored value has not yet been flushed.
-/
theorem GroupNode.PendingTracks.allSettled
    (node : GroupNode) (settled : List Occurrence)
    (tracks : node.PendingTracks settled) (zero : node.pending = 0)
    : ∀ occurrence ∈ node.tasks, occurrence ∈ settled := by
  classical
  have empty : node.tasks.filter (fun task => decide (task ∉ settled)) = [] := by
    apply List.eq_nil_of_length_eq_zero
    change unsettledCount node.tasks settled = 0
    rw [← tracks]
    exact zero
  intro occurrence member
  by_cases present : occurrence ∈ settled
  · exact present
  · have filtered : occurrence ∈ node.tasks.filter
        (fun task => decide (task ∉ settled)) := by
      exact List.mem_filter.mpr ⟨member, by simp [present]⟩
    rw [empty] at filtered
    cases filtered

/-- The proof-only ledger states the pending-count equation for every live
group. Its settled list is an external observation, not executable queue state.
-/
def State.PendingTracks (queue : State) (settled : List Occurrence) : Prop :=
  ∀ node ∈ queue.groupNodes, node.PendingTracks settled

/-- During a shared-task settlement, contributing groups are decremented one
at a time. This proof-only ledger records which groups have already seen it.
-/
private def State.PendingTracksByGroup (queue : State) (settled : Nat → List Occurrence)
    : Prop :=
  ∀ node ∈ queue.groupNodes, node.PendingTracks (settled node.group.node.ref)

/-- The live memberships of one task are exactly its contributing group refs.
This is a proof-side ownership assertion, not additional queue storage.
-/
def State.OwnedExactlyBy (queue : State) (occurrence : Occurrence) (refs : NodeRefs)
    : Prop :=
  ∀ node ∈ queue.groupNodes, occurrence ∈ node.tasks ↔ node.group.node.ref ∈ refs

/-- Decrementing only a group's pending counter preserves its task ownership
map when live delivery refs are unique.
-/
theorem State.OwnedExactlyBy.putPending {queue : State}
    {occurrence : Occurrence} {refs : NodeRefs}
    (owned : queue.OwnedExactlyBy occurrence refs)
    (unique : queue.GroupRefsUnique)
    (node : GroupNode) (nodeMember : node ∈ queue.groupNodes)
    (pending : Nat)
    : (queue.putGroupNode { node with pending }).OwnedExactlyBy occurrence refs := by
  intro next nextMember
  change next ∈ queue.groupNodes.map
    (fun old => if old.group.node.ref == node.group.node.ref then
      { node with pending } else old) at nextMember
  obtain ⟨old, oldMember, same⟩ := List.mem_map.mp nextMember
  split at same
  · rename_i sameRef
    have oldRef : old.group.node.ref = node.group.node.ref :=
      beq_iff_eq.mp sameRef
    have oldNode : old = node :=
      unique.sameNode oldMember nodeMember oldRef
    subst old
    subst next
    exact owned node nodeMember
  · subst next
    exact owned old oldMember

/-- The global ledger is the constant per-group ledger before or after an
entire shared-task settlement.
-/
theorem State.PendingTracks.toByGroup {queue : State}
    {settled : List Occurrence} (tracks : queue.PendingTracks settled)
    : queue.PendingTracksByGroup (fun _ => settled) :=
  tracks

/-- Mark one group's settlement without changing any other group's ledger. -/
def markGroupSettled (settled : Nat → List Occurrence)
    (ref : NodeRef) (occurrence : Occurrence)
    : Nat → List Occurrence :=
  fun candidate =>
    if candidate = ref then occurrence :: settled candidate else settled candidate

/-- Replay the per-group settlement marks in the same order as the queue's
contributing-group fold.
-/
def markGroupsSettled (settled : Nat → List Occurrence)
    (refs : NodeRefs) (occurrence : Occurrence)
    : Nat → List Occurrence :=
  refs.foldl (fun current ref => markGroupSettled current ref occurrence) settled

/-- Distinct contributing refs each receive one settlement mark, regardless
of their order; every other group's ledger coordinate is untouched.
-/
theorem markGroupsSettled_at (settled : Nat → List Occurrence)
    (refs : NodeRefs) (occurrence : Occurrence) (unique : refs.Nodup)
    (ref : NodeRef)
    : markGroupsSettled settled refs occurrence ref
      = if ref ∈ refs then occurrence :: settled ref else settled ref := by
  induction refs generalizing settled with
  | nil => simp [markGroupsSettled]
  | cons head tail ih =>
      obtain ⟨headAbsent, tailUnique⟩ := List.nodup_cons.mp unique
      change markGroupsSettled (markGroupSettled settled head occurrence)
        tail occurrence ref = _
      rw [ih (markGroupSettled settled head occurrence) tailUnique]
      by_cases inTail : ref ∈ tail
      · have different : ref ≠ head := by
          intro equal
          subst ref
          exact headAbsent inTail
        simp [inTail, markGroupSettled, different]
      · by_cases atHead : ref = head
        · subst ref
          simp [inTail, markGroupSettled]
        · simp [inTail, atHead, markGroupSettled]

/-- After all distinct contributing groups have been decremented, their
per-group ledger collapses back to the global settled history. Live groups
outside that contributor set must not contain the settled occurrence.
-/
theorem State.PendingTracksByGroup.toGlobalAfterSettlement {queue : State}
    {settled : List Occurrence} {refs : NodeRefs} {occurrence : Occurrence}
    (tracks
      : queue.PendingTracksByGroup (markGroupsSettled (fun _ => settled) refs occurrence))
    (unique : refs.Nodup)
    (covered
      : ∀ node ∈ queue.groupNodes, occurrence ∈ node.tasks → node.group.node.ref ∈ refs)
    : queue.PendingTracks (occurrence :: settled) := by
  intro node nodeMember
  have nodeTracks := tracks node nodeMember
  rw [markGroupsSettled_at (fun _ => settled) refs occurrence unique
    node.group.node.ref] at nodeTracks
  by_cases inRefs : node.group.node.ref ∈ refs
  · simpa [inRefs] using nodeTracks
  · have absent : occurrence ∉ node.tasks := by
      intro member
      exact inRefs (covered node nodeMember member)
    simp only [inRefs, ↓reduceIte] at nodeTracks
    change node.pending = unsettledCount node.tasks (occurrence :: settled)
    rw [unsettledCount_settle_absent node.tasks settled occurrence absent]
    exact nodeTracks

/-- A group-node replacement can advance precisely its own ledger coordinate. -/
theorem State.PendingTracksByGroup.putGroupNodeSettled {queue : State}
    {settled : Nat → List Occurrence}
    (tracks : queue.PendingTracksByGroup settled)
    (updated : GroupNode) (occurrence : Occurrence)
    (balanced : updated.PendingTracks (occurrence :: settled updated.group.node.ref))
    : (queue.putGroupNode updated).PendingTracksByGroup
        (markGroupSettled settled updated.group.node.ref occurrence) := by
  intro node member
  change node ∈ queue.groupNodes.map
    (fun old => if old.group.node.ref == updated.group.node.ref then updated else old)
    at member
  obtain ⟨old, oldMember, same⟩ := List.mem_map.mp member
  split at same
  · subst node
    simpa [markGroupSettled] using balanced
  · rename_i different
    subst node
    have unequal : old.group.node.ref ≠ updated.group.node.ref := by
      intro equal
      have sameRef : (old.group.node.ref == updated.group.node.ref) = true :=
        beq_iff_eq.mpr equal
      simp [sameRef] at different
    simpa [markGroupSettled, unequal] using tracks old oldMember

/-- A missing group ref can be marked settled without changing any live
group's ledger coordinate.
-/
theorem State.PendingTracksByGroup.markAbsentRef {queue : State}
    {settled : Nat → List Occurrence}
    (tracks : queue.PendingTracksByGroup settled)
    (ref : NodeRef) (occurrence : Occurrence)
    (missing : queue.groupNode? ref = none)
    : queue.PendingTracksByGroup (markGroupSettled settled ref occurrence) := by
  intro node member
  have missingRaw : queue.groupNodes.find?
      (fun candidate => candidate.group.node.ref == ref) = none := missing
  have noMatch := (List.find?_eq_none.mp missingRaw) node member
  have different : node.group.node.ref ≠ ref := by
    intro equal
    exact noMatch (beq_iff_eq.mpr equal)
  simpa [markGroupSettled, different] using tracks node member

/-- One successful settlement decrements one contributing group and records
that occurrence only at this group's ledger coordinate. This is the atomic
step used by the implementation's group fold.
-/
theorem State.PendingTracksByGroup.settleGroup {queue : State}
    {settled : Nat → List Occurrence}
    (tracks : queue.PendingTracksByGroup settled)
    (node : GroupNode) (nodeMember : node ∈ queue.groupNodes)
    (occurrence : Occurrence) (unique : node.tasks.Nodup)
    (member : occurrence ∈ node.tasks)
    (fresh : occurrence ∉ settled node.group.node.ref)
    : (queue.putGroupNode { node with pending := node.pending - 1 }).PendingTracksByGroup
        (markGroupSettled settled node.group.node.ref occurrence) := by
  apply tracks.putGroupNodeSettled
  exact GroupNode.PendingTracks.settle node
    (settled node.group.node.ref) occurrence
    (tracks node nodeMember) unique member fresh

/-- Decrement the pending counter for one contributing ref, if that group is
still live. This is definitionally the first fold in `State.taskSuccess`.
-/
def settleGroupRef (queue : State) (ref : NodeRef) : State :=
  match queue.groupNode? ref with
  | none => queue
  | some node => queue.putGroupNode { node with pending := node.pending - 1 }

/-- The executable contributor fold preserves exact accounting, unique
memberships and refs, and task ownership. The ledger tracks partial progress
without treating a shared task as settled for co-owners prematurely.
-/
private theorem State.settleGroupRefs_tracks
    (queue : State) (settled : Nat → List Occurrence)
    (occurrence : Occurrence) (owners refs : NodeRefs)
    (tracks : queue.PendingTracksByGroup settled)
    (refUnique : queue.GroupRefsUnique)
    (taskUnique : queue.TaskMembershipsUnique)
    (owned : queue.OwnedExactlyBy occurrence owners)
    (unique : refs.Nodup)
    (included : ∀ ref ∈ refs, ref ∈ owners)
    (fresh : ∀ ref ∈ refs, occurrence ∉ settled ref)
    : let final := refs.foldl settleGroupRef queue
      final.PendingTracksByGroup (markGroupsSettled settled refs occurrence)
      ∧ final.GroupRefsUnique
      ∧ final.TaskMembershipsUnique
      ∧ final.OwnedExactlyBy occurrence owners := by
  induction refs generalizing queue settled with
  | nil =>
      exact ⟨tracks, refUnique, taskUnique, owned⟩
  | cons head tail ih =>
      obtain ⟨headAbsent, tailUnique⟩ := List.nodup_cons.mp unique
      have headIncluded : head ∈ owners := included head (by simp)
      have headFresh : occurrence ∉ settled head := fresh head (by simp)
      have tailIncluded : ∀ ref ∈ tail, ref ∈ owners := by
        intro ref member
        exact included ref (by simp [member])
      have tailFresh : ∀ ref ∈ tail,
          occurrence ∉ markGroupSettled settled head occurrence ref := by
        intro ref member
        have different : ref ≠ head := by
          intro equal
          subst ref
          exact headAbsent member
        simpa [markGroupSettled, different] using fresh ref (by simp [member])
      let next := settleGroupRef queue head
      have nextFacts :
          next.PendingTracksByGroup (markGroupSettled settled head occurrence)
          ∧ next.GroupRefsUnique
          ∧ next.TaskMembershipsUnique
          ∧ next.OwnedExactlyBy occurrence owners := by
        cases found : queue.groupNode? head with
        | none =>
            exact ⟨
              by
                simpa [next, settleGroupRef, found]
                  using tracks.markAbsentRef head occurrence found,
              by simpa [next, settleGroupRef, found] using refUnique,
              by simpa [next, settleGroupRef, found] using taskUnique,
              by simpa [next, settleGroupRef, found] using owned
            ⟩
        | some node =>
            have nodeMember : node ∈ queue.groupNodes :=
              List.mem_of_find?_eq_some found
            have nodeRef : node.group.node.ref = head :=
              State.groupNode?_ref found
            have taskMember : occurrence ∈ node.tasks :=
              (owned node nodeMember).2 (by simpa [nodeRef] using headIncluded)
            have nodeUnique := taskUnique node nodeMember
            have nodeFresh : occurrence ∉ settled node.group.node.ref := by
              simpa [nodeRef] using headFresh
            have settledNode := tracks.settleGroup node nodeMember occurrence
              nodeUnique taskMember nodeFresh
            have ownedNode := owned.putPending refUnique node nodeMember
              (node.pending - 1)
            have uniqueNode := taskUnique.putGroupNode
              { node with pending := node.pending - 1 } nodeUnique
            have refNode := refUnique.putGroupNode
              { node with pending := node.pending - 1 }
            exact ⟨
              by simpa [next, settleGroupRef, found, nodeRef] using settledNode,
              by simpa [next, settleGroupRef, found] using refNode,
              by simpa [next, settleGroupRef, found] using uniqueNode,
              by simpa [next, settleGroupRef, found] using ownedNode
            ⟩
      obtain ⟨nextTracks, nextRefUnique, nextTaskUnique, nextOwned⟩ := nextFacts
      have tailFacts := ih next (markGroupSettled settled head occurrence)
        nextTracks nextRefUnique nextTaskUnique nextOwned
        tailUnique tailIncluded tailFresh
      simpa only [List.foldl_cons, markGroupsSettled, List.foldl_cons] using tailFacts

/-- Once every distinct contributor ref has been visited, the partial ledger
becomes the ordinary global settled-task ledger again.
-/
private theorem State.settleGroupRefs_global
    (queue : State) (settled : List Occurrence)
    (occurrence : Occurrence) (refs : NodeRefs)
    (tracks : queue.PendingTracks settled)
    (refUnique : queue.GroupRefsUnique)
    (taskUnique : queue.TaskMembershipsUnique)
    (owned : queue.OwnedExactlyBy occurrence refs)
    (unique : refs.Nodup) (fresh : occurrence ∉ settled)
    : let final := refs.foldl settleGroupRef queue
      final.PendingTracks (occurrence :: settled)
      ∧ final.GroupRefsUnique
      ∧ final.TaskMembershipsUnique
      ∧ final.OwnedExactlyBy occurrence refs := by
  have folded := queue.settleGroupRefs_tracks (fun _ => settled)
    occurrence refs refs tracks.toByGroup refUnique taskUnique owned
    unique (by intro ref member; exact member)
    (by intro ref member; exact fresh)
  obtain ⟨partialTracks, finalRefs, finalTasks, finalOwned⟩ := folded
  have global := partialTracks.toGlobalAfterSettlement unique
    (by
      intro node member taskMember
      exact (finalOwned node member).1 taskMember)
  exact ⟨global, finalRefs, finalTasks, finalOwned⟩

/-- The implementation's delivery-node fold is the ref-only settlement fold;
node metadata other than the ref is not inspected by this transition.
-/
theorem settleDeliveryGroups_eq_settleGroupRefs
    (queue : State) (groups : List Execution.DeliveryNode)
    : groups.foldl
        (fun current group =>
          match current.groupNode? group.ref with
          | none => current
          | some node =>
              current.putGroupNode { node with pending := node.pending - 1 }) queue
      = (groups.map Execution.DeliveryNode.ref).foldl settleGroupRef queue := by
  induction groups generalizing queue with
  | nil => rfl
  | cons group rest ih =>
      simp only [List.foldl_cons, List.map_cons]
      change rest.foldl
          (fun current group =>
            match current.groupNode? group.ref with
            | none => current
            | some node => current.putGroupNode
                { node with pending := node.pending - 1 })
          (settleGroupRef queue group.ref)
        = (rest.map Execution.DeliveryNode.ref).foldl settleGroupRef
            (settleGroupRef queue group.ref)
      exact ih (settleGroupRef queue group.ref)

/-- The first fold of `State.taskSuccess` advances the global ledger exactly
once for the task, despite decrementing several shared owners individually.
-/
theorem State.settleTaskGroups_global
    (queue : State) (settled : List Occurrence)
    (occurrence : Occurrence) (groups : List Execution.DeliveryNode)
    (tracks : queue.PendingTracks settled)
    (refUnique : queue.GroupRefsUnique)
    (taskUnique : queue.TaskMembershipsUnique)
    (owned : queue.OwnedExactlyBy occurrence (groups.map Execution.DeliveryNode.ref))
    (unique : (groups.map Execution.DeliveryNode.ref).Nodup)
    (fresh : occurrence ∉ settled)
    : let final :=
        groups.foldl
          (fun current group =>
            match current.groupNode? group.ref with
            | none => current
            | some node =>
                current.putGroupNode { node with pending := node.pending - 1 }) queue
      final.PendingTracks (occurrence :: settled)
      ∧ final.GroupRefsUnique
      ∧ final.TaskMembershipsUnique
      ∧ final.OwnedExactlyBy occurrence (groups.map Execution.DeliveryNode.ref) := by
  rw [settleDeliveryGroups_eq_settleGroupRefs]
  exact queue.settleGroupRefs_global settled occurrence
    (groups.map Execution.DeliveryNode.ref)
    tracks refUnique taskUnique owned unique fresh

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
