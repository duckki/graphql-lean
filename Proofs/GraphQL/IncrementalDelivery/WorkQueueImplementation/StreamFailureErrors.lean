import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ExecutedTaskErrors
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamFailureCuts

/-! Selected stream failure causes for output-aligned failure cuts. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Each stream failure contributes only to its own, uniquely closed stream ref
-----------------------------------------------------------------------------------------

/-- Distinct ordered stream closures have distinct refs.
Witness: the earlier closing action forbids the later action's ref.
-/
theorem streamFailure_refs_ne {events : List Execution.WorkQueueEvent}
    (ordered : (events.filterMap streamAction).Pairwise StreamAction.Before)
    {first second : Nat} {left right leftErrors rightErrors}
    (atLeft : events[first]? = some (.streamFailure left leftErrors))
    (atRight : events[second]? = some (.streamFailure right rightErrors))
    (earlier : first < second)
    : left.ref ≠ right.ref := by
  obtain ⟨leftBound, leftEq⟩ := List.getElem?_eq_some_iff.mp atLeft
  obtain ⟨rightBound, rightEq⟩ := List.getElem?_eq_some_iff.mp atRight
  have relation := (List.pairwise_filterMap.mp ordered).rel_getElem_of_lt
    leftBound rightBound earlier
  rw [leftEq, rightEq] at relation
  exact relation (left.ref, true) rfl (right.ref, true) rfl rfl

/-- At a selected stream failure, visible cuts are exactly its earlier labels and itself.
Witness: strict index ordering removes every later label from failedBefore.
-/
theorem StreamFailureCuts.visible_prefix {work events failures index occurrence}
    (cuts : StreamFailureCuts work events failures)
    (member : (index, occurrence) ∈ failures)
    : ∃ before after,
        failures = before ++ (index, occurrence) :: after
        ∧ failedBefore failures index = before.map Prod.snd ++ [occurrence]
        ∧ ∀ entry ∈ before, entry.1 < index := by
  obtain ⟨before, after, split⟩ := List.mem_iff_append.mp member
  have ordered := cuts.ordered
  rw [split] at ordered
  have parts := List.pairwise_append.mp ordered
  have earlier : ∀ entry ∈ before, entry.1 < index := by
    intro entry included
    exact parts.2.2 entry included _ List.mem_cons_self
  have later : ∀ entry ∈ after, index < entry.1 :=
    (List.pairwise_cons.mp parts.2.1).1
  have beforeKept : before.filter (fun entry => decide (entry.1 ≤ index)) = before := by
    apply List.filter_eq_self.mpr
    intro entry included
    simpa using Nat.le_of_lt (earlier entry included)
  have afterDropped : after.filter (fun entry => decide (entry.1 ≤ index)) = [] :=
    List.filter_eq_nil_iff.mpr (fun entry included => by
      simp [Nat.not_le.mpr (later entry included)])
  exact ⟨
    before,
    after,
    split,
    by simp [failedBefore, split, beforeKept, afterDropped],
    earlier
  ⟩

/-- A positive stream failure selects its contributing failed item from the visible cuts.
Witness: the current output's cut identifies that exact item and count; other failures
need not be summed or excluded from the inventory.
-/
theorem StreamFailureCuts.nodeErrors {work events failures index stream errors}
    (cuts : StreamFailureCuts work events failures)
    (_ordered : (events.filterMap streamAction).Pairwise StreamAction.Before)
    (atEvent : events[index]? = some (.streamFailure stream errors))
    (positive : 0 < errors)
    : NodeFailureCause work (failedBefore failures index) stream.ref errors := by
  obtain ⟨occurrence, member⟩ := cuts.covers atEvent
  obtain ⟨current, count, producer, selected, task⟩ := cuts.2 _ member
  obtain ⟨sameNode, sameCount⟩ :=
    Execution.WorkQueueEvent.streamFailure.inj (Option.some.inj (selected.symm.trans atEvent))
  subst current count
  exact ⟨
    occurrence,
    mem_failedBefore member (Nat.le_refl _),
    [stream.ref],
    producer,
    .item stream (.error errors),
    task,
    by simp,
    rfl,
    positive
  ⟩

-----------------------------------------------------------------------------------------
-- Object-task failures do not add errors to a generated stream's completion
-----------------------------------------------------------------------------------------

/-- A failed object task cannot contribute to a generated stream ref.
Witness: object ownership supplies a group descriptor, disjoint from generated stream refs.
-/
theorem ExecutedWork.objectFailure_not_streamOwner {work : Execution.Work}
    (generated : ExecutedWork work)
    {stream dependencies producer occurrence owners parent path errors}
    (streamKnown : NodeAt work stream .stream dependencies producer)
    (known : TaskAt work occurrence owners parent (.object path (.error errors)))
    : stream.ref ∉ owners := by
  intro owner
  cases occurrence with
  | item address ordinal =>
      obtain ⟨node, entries, enclosing, result, children, located, entry, _, impossible⟩ := known
      cases impossible
  | executionGroup address =>
      obtain ⟨groups, atPath, result, children, enclosing, located, sameOwners, _⟩ := known
      rw [sameOwners] at owner
      obtain ⟨group, member, sameRef⟩ := List.mem_map.mp owner
      exact generated.groupStreamRefsDisjoint (.group located member) streamKnown sameRef

/-- A failed stream item cannot contribute to a generated group ref.
Witness: its sole owner is a stream node, disjoint from every generated group ref.
-/
theorem ExecutedWork.itemFailure_not_groupOwner {work : Execution.Work}
    (generated : ExecutedWork work)
    {group dependencies producer occurrence owners parent stream errors}
    (groupKnown : NodeAt work group .group dependencies producer)
    (known : TaskAt work occurrence owners parent (.item stream (.error errors)))
    : group.ref ∉ owners := by
  obtain ⟨sameOwners, enclosing, streamKnown⟩ := itemTask_owner_nodeAt known
  rw [sameOwners]
  intro member
  exact generated.groupStreamRefsDisjoint groupKnown streamKnown (List.mem_singleton.mp member)

/-- Adding object failure candidates preserves the selected positive stream cause.
Witness: the exact item descriptor supplies positivity in generated work; extending the
inventory retains that item without changing its count.
-/
theorem StreamFailureCuts.nodeErrors_with_objects
    {work events failures index stream errors}
    (cuts : StreamFailureCuts work events failures)
    (ordered : (events.filterMap streamAction).Pairwise StreamAction.Before)
    (generated : ExecutedWork work)
    (atEvent : events[index]? = some (.streamFailure stream errors))
    (objects : List Occurrence)
    (_knownObjects
      : ∀ occurrence ∈ objects,
          ∃ owners producer path errors,
            TaskAt work occurrence owners producer (.object path (.error errors)))
    : NodeFailureCause work (failedBefore failures index ++ objects) stream.ref
        errors := by
  obtain ⟨occurrence, member⟩ := cuts.covers atEvent
  obtain ⟨node, count, producer, selected, task⟩ := cuts.2 _ member
  obtain ⟨sameNode, sameCount⟩ :=
    Execution.WorkQueueEvent.streamFailure.inj (Option.some.inj (selected.symm.trans atEvent))
  subst node count
  exact (cuts.nodeErrors ordered atEvent (generated.taskFailure_positive task rfl)).mono
    (List.subset_append_left _ _)

/-- Reordering a failure inventory preserves an existing selected cause. -/
theorem nodeErrors_of_perm {work failures more ref errors}
    (cause : NodeFailureCause work failures ref errors) (reordered : failures.Perm more)
    : NodeFailureCause work more ref errors :=
  cause.mono reordered.subset

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
