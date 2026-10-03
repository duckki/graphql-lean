import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupFailureBlocks
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.FailureTotals

/-! Candidate object-failure cuts label source settlements, not their completion notices. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- One label at each failed object handler's starting unbatched output index
-----------------------------------------------------------------------------------------

/-- Select the failed object-task identity; stream failures have their own item witnesses. -/
def GraphEvent.objectFailure? : GraphEvent → Option Occurrence
  | .taskFailure occurrence _ => some occurrence
  | _ => none

/-- Record each retained failed object settlement at the start of its atomic output block.
Silent blocks may share an index or end at the final boundary. These are candidates only:
source matching proves failure provenance, not an open owner or cancellation safety.
-/
def sourceObjectFailureCuts (offset : Nat) : List SourceOutputBlock → FailureCuts
  | [] => []
  | block :: rest =>
      let later := sourceObjectFailureCuts (offset + block.2.length) rest
      match block.1.bind GraphEvent.objectFailure? with
      | none => later
      | some occurrence => (offset, occurrence) :: later

/-- Candidate occurrences are exactly the retained failed object-source identities.
Witness: each block either contributes its one failure identity or advances only the offset.
-/
theorem sourceObjectFailureCuts_occurrences (offset : Nat)
    (blocks : List SourceOutputBlock)
    : (sourceObjectFailureCuts offset blocks).map Prod.snd
      = (blocks.filterMap Prod.fst).filterMap GraphEvent.objectFailure? := by
  induction blocks generalizing offset with
  | nil => rfl
  | cons block rest ih =>
      cases source : block.1 with
      | none => simp [sourceObjectFailureCuts, source, ih]
      | some event =>
          cases event <;> simp [sourceObjectFailureCuts, source, GraphEvent.objectFailure?, ih]
            <;> simp [List.filterMap_cons, GraphEvent.objectFailure?]

/-- Every candidate index lies between the supplied offset and the end of its block list.
Witness: the cumulative sum of actual atomic block lengths, retaining zero-width blocks.
-/
theorem sourceObjectFailureCuts_bounds (offset : Nat) (blocks : List SourceOutputBlock)
    : ∀ entry ∈ sourceObjectFailureCuts offset blocks,
        offset ≤ entry.1 ∧ entry.1 ≤ offset + (blocks.flatMap Prod.snd).length := by
  induction blocks generalizing offset with
  | nil => simp [sourceObjectFailureCuts]
  | cons block rest ih =>
      have tailBound (entry) (member : entry ∈ sourceObjectFailureCuts
          (offset + block.2.length) rest)
          : offset ≤ entry.1
            ∧ entry.1 ≤ offset + ((block :: rest).flatMap Prod.snd).length := by
        have bounds := ih _ entry member
        simp only [List.flatMap_cons, List.length_append]
        omega
      simp only [sourceObjectFailureCuts]
      split
      · exact tailBound
      · intro entry member
        rcases List.mem_cons.mp member with same | later
        · subst entry
          simp
        · exact tailBound entry later

/-- Candidate cut indices are nondecreasing, even across silent handlers.
Witness: every later cut lies beyond the current block's end; source order is retained.
-/
theorem sourceObjectFailureCuts_ordered (offset : Nat) (blocks : List SourceOutputBlock)
    : (sourceObjectFailureCuts offset blocks).Pairwise
        (fun first second => first.1 ≤ second.1) := by
  induction blocks generalizing offset with
  | nil => exact .nil
  | cons block rest ih =>
      simp only [sourceObjectFailureCuts]
      split
      · exact ih _
      · apply List.pairwise_cons.mpr
        refine ⟨?_, ih _⟩
        intro later member
        exact Nat.le_trans (Nat.le_add_right _ _)
          (sourceObjectFailureCuts_bounds _ _ later member).1

/-- Concatenating block lists shifts only the later list's starting offset.
Witness: recursion over source blocks and associativity of accumulated atom counts.
-/
theorem sourceObjectFailureCuts_append (offset : Nat)
    (before after : List SourceOutputBlock)
    : sourceObjectFailureCuts offset (before ++ after)
      = sourceObjectFailureCuts offset before
        ++ sourceObjectFailureCuts (offset + (before.flatMap Prod.snd).length) after := by
  induction before generalizing offset with
  | nil => simp [sourceObjectFailureCuts]
  | cons block rest ih =>
      simp only [List.cons_append, sourceObjectFailureCuts, List.flatMap_cons,
        List.length_append]
      split <;> simp [ih, Nat.add_assoc]

/-- A failed handler contributes a cut at precisely its source block's starting index.
Witness: split the block list at that handler, preserving all prior atomic output lengths.
-/
theorem sourceObjectFailureCuts_at (offset : Nat) (before after : List SourceOutputBlock)
    (events : List Execution.WorkQueueEvent) (occurrence : Occurrence) (errors : Nat)
    : (offset + (before.flatMap Prod.snd).length, occurrence)
      ∈ sourceObjectFailureCuts offset
          (before ++ (some (.taskFailure occurrence errors), events) :: after) := by
  rw [sourceObjectFailureCuts_append]
  apply List.mem_append_right
  simp [sourceObjectFailureCuts, GraphEvent.objectFailure?]

-----------------------------------------------------------------------------------------
-- Visibility is fixed by the handler containing the selected atomic output
-----------------------------------------------------------------------------------------

/-- Inside a handler's output, visible object cuts are exactly earlier handlers plus itself.
Witness: every earlier boundary is already reached, whereas the next handler starts after
this block's final atom. Later silent settlements cannot affect an earlier closure.
-/
theorem sourceObjectFailureCuts_visible (offset : Nat)
    (before after : List SourceOutputBlock) (block : SourceOutputBlock) (index : Nat)
    (inside : index < block.2.length)
    : failedBefore (sourceObjectFailureCuts offset (before ++ block :: after))
        (offset + (before.flatMap Prod.snd).length + index)
      = (sourceObjectFailureCuts offset before).map Prod.snd
        ++ (block.1.bind GraphEvent.objectFailure?).toList := by
  let boundary := offset + (before.flatMap Prod.snd).length
  have kept : (sourceObjectFailureCuts offset before).filter
      (fun entry => decide (entry.1 ≤ boundary + index))
      = sourceObjectFailureCuts offset before := by
    apply List.filter_eq_self.mpr
    intro entry member
    have bound := (sourceObjectFailureCuts_bounds offset before entry member).2
    simpa using Nat.le_trans bound (Nat.le_add_right boundary index)
  have dropped : (sourceObjectFailureCuts (boundary + block.2.length) after).filter
      (fun entry => decide (entry.1 ≤ boundary + index)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro entry member
    have bound := (sourceObjectFailureCuts_bounds _ _ entry member).1
    have later : ¬ entry.1 ≤ boundary + index := by omega
    simp [later]
  change failedBefore _ (boundary + index) = _
  rw [sourceObjectFailureCuts_append]
  change failedBefore (sourceObjectFailureCuts offset before ++
    sourceObjectFailureCuts boundary (block :: after)) (boundary + index) = _
  simp only [failedBefore, List.filter_append, kept, List.map_append, sourceObjectFailureCuts]
  split
  · rename_i absent
    rw [absent]
    simp [dropped]
  · rename_i occurrence selected
    rw [selected]
    simp [dropped]

-----------------------------------------------------------------------------------------
-- Source identity freshness gives occurrence uniqueness without assuming licensed cuts
-----------------------------------------------------------------------------------------

/-- Failed object identities are a subsequence of the source's full task/item identities.
Witness: taskFailure retains its singleton; other events contribute no selected failure.
-/
theorem GraphEvent.objectFailures_sublist (events : List GraphEvent)
    : (events.filterMap GraphEvent.objectFailure?).Sublist
        (events.flatMap (fun event => event.identities.1)) := by
  induction events with
  | nil => exact .slnil
  | cons event rest ih =>
      cases event <;> simp only [List.filterMap_cons, GraphEvent.objectFailure?,
        List.flatMap_cons, GraphEvent.identities, List.singleton_append, List.nil_append]
      · exact ih.cons _
      · exact ih.cons_cons _
      · exact (List.sublist_append_right _ _).trans (List.Sublist.append (.refl _) ih)
      · exact ih
      · exact ih

/-- A selected source failure identity comes from a taskFailure with some exact error count.
Witness: case analysis on the source constructor; no payload equality is used to pick tasks.
-/
theorem GraphEvent.objectFailure?_eq_some {event : GraphEvent} {occurrence : Occurrence}
    : event.objectFailure? = some occurrence
      ↔ ∃ errors, event = .taskFailure occurrence errors := by
  cases event <;> simp [GraphEvent.objectFailure?]

/-- Every candidate cut retains an actual failed source settlement, including its count.
Witness: the occurrence projection and failure-constructor inversion recover the source label.
-/
theorem sourceObjectFailureCuts_source {offset blocks entry}
    (member : entry ∈ sourceObjectFailureCuts offset blocks)
    : ∃ errors, GraphEvent.taskFailure entry.2 errors ∈ blocks.filterMap Prod.fst := by
  have projected := List.mem_map_of_mem (f := Prod.snd) member
  rw [sourceObjectFailureCuts_occurrences] at projected
  obtain ⟨event, included, selected⟩ := List.mem_filterMap.mp projected
  obtain ⟨errors, same⟩ := GraphEvent.objectFailure?_eq_some.mp selected
  subst event
  exact ⟨errors, included⟩

/-- Actual replay's candidate object cuts have distinct source-task occurrences.
Witness: block source labels embed in the inputs; source freshness covers all task identities.
-/
theorem createWorkQueue_sourceObjectFailureCuts_unique {work : Execution.Work}
    {batches : List (List GraphEvent)} (valid : ValidGraphEvents work batches.flatten)
    : let queue := State.initialize (Work.fromExecution work)
      let publisher : IncrementalPublisher :=
        { active := queue.initialGroups ++ queue.initialStreams }
      let blocks := (queue.sourceRunBlocks publisher batches).2.2
      ((sourceObjectFailureCuts 0 blocks).map Prod.snd).Nodup := by
  dsimp only
  rw [sourceObjectFailureCuts_occurrences]
  apply List.Nodup.sublist ?_ valid.identities_nodup.1
  exact ((State.sourceRunBlocks_inputs _ _ _).filterMap GraphEvent.objectFailure?).trans
    (GraphEvent.objectFailures_sublist _)

/-- Actual candidate object cuts identify fixed failed, reachable tasks inside the output.
Witness: source-label provenance and readiness supply the task; runner agreement transports
the boundary bound to its exact atomic history. Licensing is deliberately not asserted.
-/
theorem createWorkQueue_sourceObjectFailureCuts_origin {work : Execution.Work}
    {batches : List (List GraphEvent)} (generated : ExecutedWork work)
    (valid : ValidGraphEvents work batches.flatten)
    : let queue := State.initialize (Work.fromExecution work)
      let publisher : IncrementalPublisher :=
        { active := queue.initialGroups ++ queue.initialStreams }
      let blocks := (queue.sourceRunBlocks publisher batches).2.2
      ∀ entry ∈ sourceObjectFailureCuts 0 blocks,
        entry.1
          ≤ ((queue.runNormalized batches).2.flatten.flatMap publicationAtoms).length
        ∧ ∃ owners producer path errors,
            TaskAt work entry.2 owners producer (.object path (.error errors))
            ∧ Reachable work entry.2 := by
  dsimp only
  intro entry member
  obtain ⟨errors, source⟩ := sourceObjectFailureCuts_source member
  have received := (State.sourceRunBlocks_inputs _ _ _).subset source
  obtain ⟨owners, producer, path, known⟩ := valid.eachMatches received
  refine ⟨?_, owners, producer, path, errors, known,
    valid.taskFailure_reachable generated received⟩
  have bound := (sourceObjectFailureCuts_bounds _ _ entry member).2
  simpa only [Nat.zero_add, (State.sourceRunBlocks_agrees _ _).2] using bound

-----------------------------------------------------------------------------------------
-- Every emitted total draws only on source cuts visible at its actual output position
-----------------------------------------------------------------------------------------

/-- Every contributor to an emitted group total has its candidate cut already visible.
Witness: exact block-prefix totals and the cut visibility equation. A completion can sum
several earlier failures, including failures from silent handlers; it cannot use later ones.
This is inclusion, not completeness of the total against all owning visible failures.
-/
theorem sourceObjectFailureCuts_contributions {work : Execution.Work}
    {blocks : List SourceOutputBlock}
    (totals : SourceBlocksHaveFailureTotals work [] blocks) (offset : Nat)
    {index : Nat} {group : Execution.DeliveryNode} {errors : Nat}
    (atEvent : (blocks.flatMap Prod.snd)[index]? = some (.groupFailure group errors))
    : ∃ parts : List (Occurrence × Nat),
        parts ≠ []
        ∧ (parts.map Prod.fst).Nodup
        ∧ (parts.map Prod.snd).sum = errors
        ∧ ∀ occurrence count,
            (occurrence, count) ∈ parts
            → occurrence
                ∈ failedBefore (sourceObjectFailureCuts offset blocks) (offset + index)
              ∧ ∃ owners producer path,
                  TaskAt work occurrence owners producer (.object path (.error count))
                  ∧ group.ref ∈ owners := by
  obtain ⟨before, block, after, localIndex, same, position, atLocal⟩ :=
    sourceOutputBlocks_at atEvent
  subst blocks
  have exactTotal := totals.atBlock (List.mem_of_getElem? atLocal)
  obtain ⟨parts, nonempty, unique, sum, sources⟩ := exactTotal
  refine ⟨parts, nonempty, unique, sum, ?_⟩
  intro occurrence count member
  obtain ⟨source, known⟩ := sources occurrence count member
  refine ⟨?_, known⟩
  have visible := sourceObjectFailureCuts_visible offset before after block localIndex
    (List.getElem?_eq_some_iff.mp atLocal).1
  rw [position, ← Nat.add_assoc, visible, sourceObjectFailureCuts_occurrences]
  have projected : occurrence ∈
      (before.filterMap Prod.fst ++ block.1.toList).filterMap GraphEvent.objectFailure? :=
    List.mem_filterMap.mpr ⟨.taskFailure occurrence count, by simpa using source, rfl⟩
  cases label : block.1 with
  | none => simpa [List.filterMap_append, label] using projected
  | some event =>
      cases event <;>
        simpa [List.filterMap_append, label, GraphEvent.objectFailure?] using projected

/-- Each group failure sees at least one matching contributor's source-task candidate cut.
Witness: choose from the nonempty exact contribution inventory, not from the current input.
The chosen task's count need not equal the accumulated completion's total.
-/
theorem sourceObjectFailureCuts_covers {work : Execution.Work}
    {blocks : List SourceOutputBlock}
    (totals : SourceBlocksHaveFailureTotals work [] blocks) (offset : Nat) {index : Nat}
    {group : Execution.DeliveryNode} {errors : Nat}
    (atEvent : (blocks.flatMap Prod.snd)[index]? = some (.groupFailure group errors))
    : ∃ cut occurrence count owners producer path,
        (cut, occurrence) ∈ sourceObjectFailureCuts offset blocks
        ∧ cut ≤ offset + index
        ∧ TaskAt work occurrence owners producer (.object path (.error count))
        ∧ group.ref ∈ owners := by
  obtain ⟨parts, nonempty, _, _, contributions⟩ :=
    sourceObjectFailureCuts_contributions totals offset atEvent
  obtain ⟨⟨occurrence, count⟩, member⟩ := List.exists_mem_of_ne_nil parts nonempty
  obtain ⟨visible, owners, producer, path, known, owner⟩ :=
    contributions occurrence count member
  obtain ⟨⟨cut, task⟩, selected, same⟩ := List.mem_map.mp visible
  dsimp only at same
  subst task
  obtain ⟨recorded, reached⟩ := List.mem_filter.mp selected
  exact ⟨cut, occurrence, count, owners, producer, path, recorded,
    of_decide_eq_true reached, known, owner⟩

/-- Every actual group total has a distinct exact inventory inside its visible object cuts.
Witness: generated replay supplies block-prefix totals; runner agreement retains the index.
General contributor completeness and failure-cut licensing are not assumed or established.
-/
theorem createWorkQueue_sourceObjectFailureCuts_contributions {work : Execution.Work}
    (generated : ExecutedWork work) {batches : List (List GraphEvent)}
    (valid : ValidGraphEvents work batches.flatten)
    {index : Nat} {group : Execution.DeliveryNode} {errors : Nat}
    (atEvent
      : (((State.initialize (Work.fromExecution work)).runNormalized
            batches).2.flatten.flatMap
          publicationAtoms)[index]?
        = some (.groupFailure group errors))
    : let queue := State.initialize (Work.fromExecution work)
      let publisher : IncrementalPublisher :=
        { active := queue.initialGroups ++ queue.initialStreams }
      let blocks := (queue.sourceRunBlocks publisher batches).2.2
      ∃ parts : List (Occurrence × Nat),
        parts ≠ []
        ∧ (parts.map Prod.fst).Nodup
        ∧ (parts.map Prod.snd).sum = errors
        ∧ ∀ occurrence count,
            (occurrence, count) ∈ parts
            → occurrence ∈ failedBefore (sourceObjectFailureCuts 0 blocks) index
              ∧ ∃ owners producer path,
                  TaskAt work occurrence owners producer (.object path (.error count))
                  ∧ group.ref ∈ owners := by
  dsimp only
  simpa only [Nat.zero_add]
    using sourceObjectFailureCuts_contributions
      (createWorkQueue_sourceRunBlocks_groupFailureTotals generated valid) 0
      (index := index) (group := group) (errors := errors)
      (by rw [(State.sourceRunBlocks_agrees _ _).2]; exact atEvent)

/-- Each actual group total has an exact NodeErrors inventory inside its candidate cut.
Witness: construct the contribution function from distinct pairs and retain their proved
visibility. The complete-contributor transport lemma still needs the converse inclusion
for owning failures; this theorem alone does not count every visible candidate.
-/
theorem createWorkQueue_sourceObjectFailureCuts_nodeErrorsInventory
    {work : Execution.Work} (generated : ExecutedWork work)
    {batches : List (List GraphEvent)} (valid : ValidGraphEvents work batches.flatten)
    {index : Nat} {group : Execution.DeliveryNode} {errors : Nat}
    (atEvent
      : (((State.initialize (Work.fromExecution work)).runNormalized
            batches).2.flatten.flatMap
          publicationAtoms)[index]?
        = some (.groupFailure group errors))
    : let queue := State.initialize (Work.fromExecution work)
      let publisher : IncrementalPublisher :=
        { active := queue.initialGroups ++ queue.initialStreams }
      let blocks := (queue.sourceRunBlocks publisher batches).2.2
      ∃ failed : List Occurrence,
        failed ≠ []
        ∧ failed.Nodup
        ∧ NodeErrors work failed group.ref errors
        ∧ failed.Subset (failedBefore (sourceObjectFailureCuts 0 blocks) index) := by
  obtain ⟨parts, nonempty, unique, sum, sources⟩ :=
    createWorkQueue_sourceObjectFailureCuts_contributions generated valid atEvent
  refine ⟨parts.map Prod.fst, fun empty => nonempty (List.map_eq_nil_iff.mp empty),
    unique, ?_, ?_⟩
  · rw [← sum]
    exact failureContributions_nodeErrors parts unique
      (fun occurrence count member => (sources occurrence count member).2)
  · intro occurrence member
    obtain ⟨⟨task, count⟩, member, same⟩ := List.mem_map.mp member
    dsimp only at same
    subst task
    exact (sources occurrence count member).1

/-- Each actual group-failure atom is covered by an earlier contributing source cut.
Witness: exact runner agreement and the nonempty prefix total retain the original index.
A delayed closure can reuse earlier task cuts, and one task can justify several closures.
-/
theorem createWorkQueue_sourceObjectFailureCuts_covers {work : Execution.Work}
    (generated : ExecutedWork work)
    {batches : List (List GraphEvent)} (valid : ValidGraphEvents work batches.flatten)
    {index : Nat} {group : Execution.DeliveryNode} {errors : Nat}
    (atEvent
      : (((State.initialize (Work.fromExecution work)).runNormalized
            batches).2.flatten.flatMap
          publicationAtoms)[index]?
        = some (.groupFailure group errors))
    : let queue := State.initialize (Work.fromExecution work)
      let publisher : IncrementalPublisher :=
        { active := queue.initialGroups ++ queue.initialStreams }
      let blocks := (queue.sourceRunBlocks publisher batches).2.2
      ∃ cut occurrence count owners producer path,
        (cut, occurrence) ∈ sourceObjectFailureCuts 0 blocks
        ∧ cut ≤ index
        ∧ TaskAt work occurrence owners producer (.object path (.error count))
        ∧ group.ref ∈ owners := by
  dsimp only
  simpa only [Nat.zero_add]
    using sourceObjectFailureCuts_covers
      (createWorkQueue_sourceRunBlocks_groupFailureTotals generated valid) 0
      (index := index) (group := group) (errors := errors)
      (by rw [(State.sourceRunBlocks_agrees _ _).2]; exact atEvent)

/-- Actual failed group closures have a historical failure under the candidate object cuts.
Witness: some contributing source cut is visible before closure; several closures can
reuse it. No matching-specific or admitted-history premise is used. Licensing all candidate
cuts, including cancellation safety and open owners, remains a separate obligation.
-/
theorem createWorkQueue_sourceObjectFailureCuts_nodeFailed {work : Execution.Work}
    (generated : ExecutedWork work)
    {batches : List (List GraphEvent)} (valid : ValidGraphEvents work batches.flatten)
    (matching : PublicationMatching) {index : Nat} {group : Execution.DeliveryNode}
    {errors : Nat}
    (atEvent
      : (((State.initialize (Work.fromExecution work)).runNormalized
            batches).2.flatten.flatMap
          publicationAtoms)[index]?
        = some (.groupFailure group errors))
    : let queue := State.initialize (Work.fromExecution work)
      let publisher : IncrementalPublisher :=
        { active := queue.initialGroups ++ queue.initialStreams }
      let blocks := (queue.sourceRunBlocks publisher batches).2.2
      NodeFailed work matching
        (((queue.runNormalized batches).2.flatten.flatMap publicationAtoms).take index)
        (sourceObjectFailureCuts 0 blocks) group.ref := by
  obtain ⟨cut, occurrence, count, owners, producer, path, member, visible, known, owner⟩ :=
    createWorkQueue_sourceObjectFailureCuts_covers generated valid atEvent
  apply NodeFailed.task known owner
  have length :
      ((((State.initialize (Work.fromExecution work)).runNormalized batches).2.flatten.flatMap
          publicationAtoms).take index).length = index :=
    List.length_take_of_le (Nat.le_of_lt (List.getElem?_eq_some_iff.mp atEvent).1)
  rw [length]
  exact mem_failedBefore member visible

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
