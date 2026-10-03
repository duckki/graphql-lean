import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamFailureAccounting

/-! Output-aligned candidate stream failure cuts, before the cancellation-safety bridge. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Label each actual stream failure once, in its original unbatched output position
-----------------------------------------------------------------------------------------

/-- The unbatched output indices carrying stream-failure notices, in increasing order. -/
def streamFailurePositions (events : List Execution.WorkQueueEvent) : List Nat :=
  (List.range events.length).filter
    fun index =>
      match events[index]? with
      | some (.streamFailure ..) => true
      | _ => false

/-- A candidate cut labels this exact stream-failure notice with a matching failed item. -/
def StreamFailureOrigin (work : Execution.Work) (events : List Execution.WorkQueueEvent)
    (entry : Nat × Occurrence)
    : Prop :=
  ∃ stream errors producer,
    events[entry.1]? = some (.streamFailure stream errors)
    ∧ TaskAt work entry.2 [stream.ref] producer (.item stream (.error errors))

/-- Candidate stream cuts cover exactly the emitted stream failures, in output order.
These proof labels do not yet assert absence of cancellation or include object failures.
-/
def StreamFailureCuts (work : Execution.Work) (events : List Execution.WorkQueueEvent)
    (failures : FailureCuts)
    : Prop :=
  failures.map Prod.fst = streamFailurePositions events
  ∧ ∀ entry ∈ failures, StreamFailureOrigin work events entry

/-- A selected index is exactly an actual stream-failure position.
Witness: the range bound follows from the successful event lookup.
-/
theorem mem_streamFailurePositions {events index}
    : index ∈ streamFailurePositions events
      ↔ ∃ stream errors, events[index]? = some (.streamFailure stream errors) := by
  constructor
  · intro member
    have selected := (List.mem_filter.mp member).2
    cases atEvent : events[index]? with
    | none => simp [atEvent] at selected
    | some event =>
        cases event <;> simp [atEvent] at selected
        exact ⟨_, _, rfl⟩
  · rintro ⟨stream, errors, atEvent⟩
    exact List.mem_filter.mpr ⟨List.mem_range.mpr (List.getElem?_eq_some_iff.mp atEvent).choose,
      by simp [atEvent]⟩

/-- Candidate cut positions strictly increase.
Witness: filtering the increasing finite index range preserves its pairwise order.
-/
theorem StreamFailureCuts.ordered {work events failures}
    (cuts : StreamFailureCuts work events failures)
    : failures.Pairwise (fun first second => first.1 < second.1) := by
  have rangeOrdered (size : Nat) : (List.range size).Pairwise (· < ·) := by
    induction size with
    | zero => exact .nil
    | succ size ih =>
        rw [List.range_succ]
        refine List.pairwise_append.mpr ⟨ih, by simp, ?_⟩
        intro first member second last
        have same := List.mem_singleton.mp last
        subst second
        exact List.mem_range.mp member
  apply List.pairwise_map.mp
  rw [cuts.1]
  exact (rangeOrdered events.length).sublist List.filter_sublist

/-- Every candidate cut is strictly inside its output history.
Witness: its origin contains the event at the cut's index.
-/
theorem StreamFailureCuts.bound {work events failures entry}
    (cuts : StreamFailureCuts work events failures) (member : entry ∈ failures)
    : entry.1 < events.length := by
  obtain ⟨stream, errors, producer, atEvent, _⟩ := cuts.2 entry member
  exact (List.getElem?_eq_some_iff.mp atEvent).choose

/-- Every emitted stream failure has one of the retained candidate labels at its position.
Witness: the exact position projection, without comparison of error counts or payloads.
-/
theorem StreamFailureCuts.covers {work events failures index stream errors}
    (cuts : StreamFailureCuts work events failures)
    (atEvent : events[index]? = some (.streamFailure stream errors))
    : ∃ occurrence, (index, occurrence) ∈ failures := by
  have member : index ∈ failures.map Prod.fst := by
    rw [cuts.1]
    exact mem_streamFailurePositions.mpr ⟨stream, errors, atEvent⟩
  obtain ⟨⟨cut, occurrence⟩, included, same⟩ := List.mem_map.mp member
  dsimp only at same
  subst cut
  exact ⟨occurrence, included⟩

/-- Ordered stream closure refs make the candidate failure occurrences distinct.
Witness: equal occurrences would have equal sole-owner refs, contradicting closure order
at their strictly increasing output indices. This does not assume failure-cut licensing.
-/
theorem StreamFailureCuts.unique {work events failures}
    (cuts : StreamFailureCuts work events failures)
    (ordered : (events.filterMap streamAction).Pairwise StreamAction.Before)
    : (failures.map Prod.snd).Nodup := by
  apply List.pairwise_map.mpr
  apply List.Pairwise.imp_of_mem (p := cuts.ordered)
  intro first second firstMember secondMember earlier same
  obtain ⟨left, leftErrors, leftProducer, atLeft, firstTask⟩ := cuts.2 first firstMember
  obtain ⟨right, rightErrors, rightProducer, atRight, secondTask⟩ := cuts.2 second secondMember
  rw [same] at firstTask
  have sameRef := (List.cons.inj (firstTask.unique secondTask).1).1
  obtain ⟨leftBound, leftEq⟩ := List.getElem?_eq_some_iff.mp atLeft
  obtain ⟨rightBound, rightEq⟩ := List.getElem?_eq_some_iff.mp atRight
  have relation := (List.pairwise_filterMap.mp ordered).rel_getElem_of_lt
    leftBound rightBound earlier
  rw [leftEq, rightEq] at relation
  exact relation (left.ref, true) rfl (right.ref, true) rfl rfl sameRef

-----------------------------------------------------------------------------------------
-- Assemble local failure evidence under the unchanged joint publication matching
-----------------------------------------------------------------------------------------

/-- Finite pointwise witnesses can be labelled without changing their index order.
Witness: list induction chooses one existing witness per index, retaining its property.
-/
private theorem choose_indexed_witnesses (indices : List Nat)
    (property : Nat → Occurrence → Prop)
    (supported : ∀ index ∈ indices, ∃ occurrence, property index occurrence)
    : ∃ entries : FailureCuts,
        entries.map Prod.fst = indices ∧ ∀ entry ∈ entries, property entry.1 entry.2 := by
  induction indices with
  | nil => exact ⟨[], rfl, by simp⟩
  | cons index rest ih =>
      obtain ⟨occurrence, known⟩ := supported index List.mem_cons_self
      obtain ⟨entries, positions, witnesses⟩ :=
        ih (fun next member => supported next (List.mem_cons_of_mem _ member))
      refine ⟨(index, occurrence) :: entries, by simp [positions], ?_⟩
      intro entry member
      rcases List.mem_cons.mp member with same | later
      · subst entry; exact known
      · exact witnesses entry later

/-- Actual stream failures admit one ordered candidate cut list under the supplied matching.
Witness: choose the exact reachable failing item at each emitted failure index. Existing
source inventory and closure-order proofs supply an open owner and exclude publication.
The missing licensing clause is cancellation safety, not ordering or failure provenance.
-/
theorem createWorkQueue_runNormalized_streamFailureCuts {work : Execution.Work}
    {batches : List (List GraphEvent)} (generated : ExecutedWork work)
    (valid : ValidGraphEvents work batches.flatten) (matching : PublicationMatching)
    (exactValues
      : let atoms :=
          ((State.initialize (Work.fromExecution work)).runNormalized
            batches).2.flatten.flatMap
            publicationAtoms
        ∀ index event,
          atoms[index]? = some event
          → IsValue event
          → PublicationAt work (matching index) event)
    (covered
      : ∀ occurrence ∈ (batches.flatten.flatMap GraphEvent.itemPublications).map Prod.fst,
          Published matching
            (((State.initialize (Work.fromExecution work)).runNormalized
                batches).2.flatten.flatMap
              publicationAtoms) occurrence)
    : let queue := State.initialize (Work.fromExecution work)
      let atoms := (queue.runNormalized batches).2.flatten.flatMap publicationAtoms
      ∃ failures : FailureCuts,
        StreamFailureCuts work atoms failures
        ∧ (failures.map Prod.snd).Nodup
        ∧ ∀ entry ∈ failures,
            Reachable work entry.2
            ∧ ¬Published matching atoms entry.2
            ∧ ∃ ref,
                TaskHasOwners work entry.2 [ref]
                ∧ Open
                    ((queue.initialGroups ++ queue.initialStreams).map
                      Execution.DeliveryNode.ref)
                    (atoms.take entry.1) ref := by
  dsimp only
  let queue := State.initialize (Work.fromExecution work)
  let atoms := (queue.runNormalized batches).2.flatten.flatMap publicationAtoms
  let property := fun index occurrence =>
    StreamFailureOrigin work atoms (index, occurrence)
    ∧ Reachable work occurrence ∧ ¬Published matching atoms occurrence
    ∧ ∃ ref, TaskHasOwners work occurrence [ref]
        ∧ Open ((queue.initialGroups ++ queue.initialStreams).map Execution.DeliveryNode.ref)
            (atoms.take index) ref
  obtain ⟨failures, positions, evidence⟩ :=
    choose_indexed_witnesses (streamFailurePositions atoms) property (by
      intro index member
      obtain ⟨stream, errors, atFailure⟩ := mem_streamFailurePositions.mp member
      obtain ⟨address, ordinal, producer, task, reachable, opened, unpublished, _⟩ :=
        createWorkQueue_runNormalized_streamFailure_accounting generated valid matching
          exactValues covered atFailure
      exact ⟨.item address ordinal, ⟨stream, errors, producer, atFailure, task⟩,
        reachable, unpublished, stream.ref, ⟨producer, _, task⟩, opened⟩)
  have cuts : StreamFailureCuts work atoms failures :=
    ⟨positions, fun entry member => (evidence entry member).1⟩
  exact ⟨failures, cuts,
    cuts.unique (createWorkQueue_runNormalized_atomicStreamActions_ordered valid),
    fun entry member => (evidence entry member).2⟩

-----------------------------------------------------------------------------------------
-- Every failure-witness clause except prior cancellation is already checked
-----------------------------------------------------------------------------------------

/-- An ordered candidate list becomes a FailureWitness exactly when none is already cancelled.
Witness: its source descriptors, reachability, open owners, and increasing output indices
discharge all other clauses. This equivalence makes the unresolved obligation explicit;
it is a proof interface, not an extra public scheduler assumption.
-/
theorem StreamFailureCuts.failureWitness_iff {work events failures initial matching}
    (cuts : StreamFailureCuts work events failures)
    (supported
      : ∀ entry ∈ failures,
          Reachable work entry.2
          ∧ ∃ ref,
              TaskHasOwners work entry.2 [ref] ∧ Open initial (events.take entry.1) ref)
    : FailureWitness work initial matching events failures
      ↔ ∀ before cut occurrence after,
          failures = before ++ (cut, occurrence) :: after
          → ¬TaskCancelled work matching (events.take cut) before occurrence := by
  constructor
  · intro witness before cut occurrence after split
    exact (witness before cut occurrence after split).2.2.2
  · intro uncancelled before cut occurrence after split
    have member : (cut, occurrence) ∈ failures := by simp [split]
    obtain ⟨stream, errors, producer, atEvent, task⟩ := cuts.2 _ member
    obtain ⟨reachable, ref, ⟨otherProducer, payload, known⟩, opened⟩ := supported _ member
    have sameRef := (List.cons.inj (task.unique known).1).1
    refine ⟨Nat.le_of_lt (cuts.bound member), ?_,
      ⟨[stream.ref], producer, _, task, rfl, reachable, stream.ref, List.mem_cons_self,
        sameRef.symm ▸ opened.1⟩,
      uncancelled before cut occurrence after split⟩
    intro earlier included
    have ordered := cuts.ordered
    rw [split] at ordered
    exact Nat.le_of_lt (ordered.rel_of_mem_append included List.mem_cons_self)

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
