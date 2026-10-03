import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamFailureCuts

/-! Exact stream error totals for output-aligned failure cuts. -/

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

/-- Each stream failure reports exactly the contributing errors in all visible stream cuts.
Witness: prior closures have different stream refs and hence contribute zero; the current
cut is the sole contributing failed item and retains its exact reported error count.
No cancellation-safety or already-admitted-history assumption is used for this count.
-/
theorem StreamFailureCuts.nodeErrors {work events failures index stream errors}
    (cuts : StreamFailureCuts work events failures)
    (ordered : (events.filterMap streamAction).Pairwise StreamAction.Before)
    (atEvent : events[index]? = some (.streamFailure stream errors))
    : NodeErrors work (failedBefore failures index) stream.ref errors := by
  classical
  obtain ⟨occurrence, member⟩ := cuts.covers atEvent
  obtain ⟨current, count, producer, selected, task⟩ := cuts.2 _ member
  have same := Execution.WorkQueueEvent.streamFailure.inj (Option.some.inj (selected.symm.trans atEvent))
  obtain ⟨sameNode, sameCount⟩ := same
  subst current count
  obtain ⟨before, after, split, visible, earlier⟩ := cuts.visible_prefix member
  have oldFacts (entry : Nat × Occurrence) (included : entry ∈ before)
      : ∃ node errors producer,
          TaskAt work entry.2 [node.ref] producer (.item node (.error errors))
          ∧ node.ref ≠ stream.ref ∧ entry.2 ≠ occurrence := by
    have member : entry ∈ failures := by rw [split]; exact List.mem_append_left _ included
    obtain ⟨node, errors, producer, atPrior, prior⟩ := cuts.2 entry member
    have different := streamFailure_refs_ne ordered atPrior atEvent (earlier entry included)
    refine ⟨node, errors, producer, prior, different, ?_⟩
    intro same
    rw [same] at prior
    exact different (List.cons.inj (prior.unique task).1).1
  let contribution := fun source => if source = occurrence then errors else 0
  rw [visible]
  refine ⟨contribution, ?_, ?_⟩
  · intro source included
    rcases List.mem_append.mp included with prior | current
    · obtain ⟨entry, inBefore, same⟩ := List.mem_map.mp prior
      subst source
      obtain ⟨node, count, producer, known, different, notCurrent⟩ := oldFacts entry inBefore
      exact ⟨[node.ref], producer, _, known, by simp [contribution, notCurrent, Ne.symm different]⟩
    · have same := List.mem_singleton.mp current
      subst source
      exact ⟨[stream.ref], producer, _, task, by simp [contribution, Payload.failure]⟩
  · have oldZero : ((before.map Prod.snd).map contribution).sum = 0 := by
      apply List.sum_eq_zero_iff_forall_eq_nat.mpr
      intro count included
      obtain ⟨source, inBefore, same⟩ := List.mem_map.mp included
      obtain ⟨entry, member, sameSource⟩ := List.mem_map.mp inBefore
      obtain ⟨node, errors, producer, known, different, notCurrent⟩ := oldFacts entry member
      rw [← same, ← sameSource]
      simp [contribution, notCurrent]
    rw [List.map_append, List.sum_append, oldZero]
    simp [contribution]

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

/-- Adding only failed object tasks leaves the exact stream error total unchanged.
Witness: generated role separation makes every added contribution zero. Existing
contributions retain their values; object tasks cannot share a stream-item occurrence.
The added failures may be reordered separately when constructing the eventual full cuts.
-/
theorem StreamFailureCuts.nodeErrors_with_objects
    {work events failures index stream errors}
    (cuts : StreamFailureCuts work events failures)
    (ordered : (events.filterMap streamAction).Pairwise StreamAction.Before)
    (generated : ExecutedWork work)
    (atEvent : events[index]? = some (.streamFailure stream errors))
    (objects : List Occurrence)
    (knownObjects
      : ∀ occurrence ∈ objects,
          ∃ owners producer path errors,
            TaskAt work occurrence owners producer (.object path (.error errors)))
    : NodeErrors work (failedBefore failures index ++ objects) stream.ref errors := by
  classical
  obtain ⟨occurrence, member⟩ := cuts.covers atEvent
  obtain ⟨node, count, producer, selected, task⟩ := cuts.2 _ member
  obtain ⟨sameNode, sameCount⟩ :=
    Execution.WorkQueueEvent.streamFailure.inj (Option.some.inj (selected.symm.trans atEvent))
  subst node count
  obtain ⟨dependencies, streamKnown⟩ := (itemTask_owner_nodeAt task).2
  obtain ⟨contribution, values, total⟩ := cuts.nodeErrors ordered atEvent
  let extended := fun source => if source ∈ objects then 0 else contribution source
  have disjoint : ∀ source ∈ failedBefore failures index, source ∉ objects := by
    intro source inCuts inObjects
    obtain ⟨entry, retained, same⟩ := List.mem_map.mp inCuts
    obtain ⟨owner, count, parent, _, descriptor⟩ := cuts.2 entry (List.mem_filter.mp retained).1
    obtain ⟨owners, otherProducer, path, errors, object⟩ := knownObjects source inObjects
    rw [same] at descriptor
    have impossible := (descriptor.unique object).2.2
    cases impossible
  refine ⟨extended, ?_, ?_⟩
  · intro source included
    rcases List.mem_append.mp included with fromStream | fromObject
    · obtain ⟨owners, parent, payload, descriptor, count⟩ := values source fromStream
      exact ⟨owners, parent, payload, descriptor, by
        simpa [extended, disjoint source fromStream] using count⟩
    · obtain ⟨owners, parent, path, count, descriptor⟩ := knownObjects source fromObject
      have absent := generated.objectFailure_not_streamOwner streamKnown descriptor
      exact ⟨owners, parent, _, descriptor, by simp [extended, fromObject, absent]⟩
  · have oldSame : (failedBefore failures index).map extended
        = (failedBefore failures index).map contribution := by
      apply List.map_congr_left
      intro source member
      simp [extended, disjoint source member]
    have newZero : (objects.map extended).sum = 0 := by
      apply List.sum_eq_zero_iff_forall_eq_nat.mpr
      intro count member
      obtain ⟨source, member, same⟩ := List.mem_map.mp member
      rw [← same]
      simp [extended, member]
    simpa only [List.map_append, List.sum_append, oldSame, newZero, Nat.add_zero] using total

/-- Reordering the full failure inventory preserves its node-error count.
Witness: retain each occurrence's exact contribution and permute the summands. This
lets object and stream failures interleave without imposing an order on error summation.
-/
theorem nodeErrors_of_perm {work failures more ref errors}
    (counts : NodeErrors work failures ref errors) (reordered : failures.Perm more)
    : NodeErrors work more ref errors := by
  obtain ⟨contribution, known, total⟩ := counts
  exact ⟨contribution, fun occurrence member => known occurrence (reordered.mem_iff.mpr member),
    total.trans (reordered.map contribution).sum_nat⟩

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
