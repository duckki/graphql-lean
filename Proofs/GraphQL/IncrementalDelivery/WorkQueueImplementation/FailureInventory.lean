import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.CompleteMixedFailureCuts

/-! One ordered complete candidate failure inventory for actual normalized replay. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Merge candidate cuts without moving any unbatched output index
-----------------------------------------------------------------------------------------

/-- Merge object and stream candidates by output index, retaining both input orders.
Object candidates precede stream candidates at equal indices. This is a proof-side
inventory construction, not an implementation scheduling policy or a licensed witness.
-/
def mergeFailureCuts (objects streams : FailureCuts) : FailureCuts :=
  objects.merge streams (fun left right => left.1 ≤ right.1)

/-- The merge retains precisely both candidate lists, with their original cut positions.
Witness: the standard merge permutation followed by append commutation.
-/
theorem mergeFailureCuts_partition (objects streams : FailureCuts)
    : (mergeFailureCuts objects streams).Perm (streams ++ objects) :=
  (List.merge_perm_append _).trans (List.perm_append_comm)

/-- Merging two ordered candidate lists retains nondecreasing cut positions.
Witness: the standard sorted-merge theorem for the total transitive order on indices.
-/
theorem mergeFailureCuts_ordered {objects streams : FailureCuts}
    (objectOrder : objects.Pairwise (fun left right => left.1 ≤ right.1))
    (streamOrder : streams.Pairwise (fun left right => left.1 ≤ right.1))
    : (mergeFailureCuts objects streams).Pairwise
        (fun left right => left.1 ≤ right.1) := by
  have trans (left middle right : Nat × Occurrence)
      : decide (left.1 ≤ middle.1) = true → decide (middle.1 ≤ right.1) = true →
          decide (left.1 ≤ right.1) = true := by
    simp only [decide_eq_true_eq]
    exact Nat.le_trans
  have total (left right : Nat × Occurrence)
      : (decide (left.1 ≤ right.1) || decide (right.1 ≤ left.1)) = true := by
    simpa only [Bool.or_eq_true, decide_eq_true_eq] using Nat.le_total left.1 right.1
  simpa only [mergeFailureCuts, decide_eq_true_eq]
    using List.pairwise_merge trans total objects streams
      (by simpa only [decide_eq_true_eq] using objectOrder)
      (by simpa only [decide_eq_true_eq] using streamOrder)

/-- A mixed candidate inventory has no repeated failed occurrence.
Witness: stream closure order and source freshness give uniqueness within each part;
fixed payload descriptors rule out an occurrence shared by an object and an item.
-/
theorem StreamFailureCuts.mixed_unique {work events}
    {streams objects failures : FailureCuts}
    (cuts : StreamFailureCuts work events streams)
    (ordered : (events.filterMap streamAction).Pairwise StreamAction.Before)
    (objectUnique : (objects.map Prod.snd).Nodup)
    (objectKnown
      : ∀ entry ∈ objects,
          ∃ owners producer path errors,
            TaskAt work entry.2 owners producer (.object path (.error errors)))
    (partition : failures.Perm (streams ++ objects))
    : (failures.map Prod.snd).Nodup := by
  apply (partition.map Prod.snd).nodup_iff.mpr
  rw [List.map_append]
  refine List.nodup_append.mpr ⟨cuts.unique ordered, objectUnique, ?_⟩
  intro first firstMember second secondMember same
  obtain ⟨streamEntry, streamMember, sameStream⟩ := List.mem_map.mp firstMember
  obtain ⟨objectEntry, objectMember, sameObject⟩ := List.mem_map.mp secondMember
  obtain ⟨stream, count, parent, _, item⟩ := cuts.2 streamEntry streamMember
  obtain ⟨owners, producer, path, errors, object⟩ := objectKnown objectEntry objectMember
  rw [sameStream, same, ← sameObject] at item
  have impossible := (item.unique object).2.2
  cases impossible

-----------------------------------------------------------------------------------------
-- The full inventory accounts for every emitted error, without assuming admission
-----------------------------------------------------------------------------------------

/-- Candidate cuts are ordered, unique, reachable failures with complete output counts.
This proof-only certificate does not assert prior notices or absence of prior cancellation.
Those are the remaining causal licensing obligations, not additional source assumptions.
-/
def CompleteFailureInventory (work : Execution.Work)
    (events : List Execution.WorkQueueEvent) (failures : FailureCuts)
    : Prop :=
  failures.Pairwise (fun left right => left.1 ≤ right.1)
  ∧ (failures.map Prod.snd).Nodup
  ∧ (∀ entry ∈ failures,
      entry.1 ≤ events.length
      ∧ Reachable work entry.2
      ∧ ∃ owners producer payload,
          TaskAt work entry.2 owners producer payload ∧ payload.failure.isSome = true)
  ∧ (∀ index group errors,
      events[index]? = some (.groupFailure group errors)
      → NodeErrors work (failedBefore failures index) group.ref errors)
  ∧ (∀ index stream errors,
      events[index]? = some (.streamFailure stream errors)
      → NodeErrors work (failedBefore failures index) stream.ref errors)

/-- Exact successful publications cannot publish any member of the failure inventory.
Witness: the inventory supplies each fixed failed payload; descriptor uniqueness excludes
the successful payload required by the independently constructed publication matching.
-/
theorem CompleteFailureInventory.unpublished {work events failures matching}
    (inventory : CompleteFailureInventory work events failures)
    (exactValues
      : ∀ index event,
          events[index]? = some event
          → IsValue event
          → PublicationAt work (matching index) event)
    {entry} (member : entry ∈ failures)
    : ¬Published matching events entry.2 := by
  obtain ⟨_, _, owners, producer, payload, known, failed⟩ := inventory.2.2.1 entry member
  exact failedTask_unpublished_of_exactValues exactValues known failed

/-- Only prior-announcement and prior-cancellation licensing remain for a complete inventory.
Witness: its bounds, ordered positions, failed descriptors, and reachability discharge
every other FailureWitness clause. This equivalence identifies obligations to prove;
it does not add assumptions to the host source or the public conformance statement.
-/
theorem CompleteFailureInventory.failureWitness_iff
    {work events failures initial matching}
    (inventory : CompleteFailureInventory work events failures)
    : FailureWitness work initial matching events failures
      ↔ (∀ entry ∈ failures,
          ∃ owners,
            TaskHasOwners work entry.2 owners
            ∧ ∃ ref ∈ owners, ref ∈ announcedRefs initial (events.take entry.1))
        ∧ (∀ before cut occurrence after,
            failures = before ++ (cut, occurrence) :: after
            → ¬TaskCancelled work matching (events.take cut) before occurrence) := by
  constructor
  · intro witness
    constructor
    · intro entry member
      obtain ⟨before, after, split⟩ := List.mem_iff_append.mp member
      obtain ⟨owners, producer, payload, task, _, _, ref, owner, announced⟩ :=
        (witness before entry.1 entry.2 after split).2.2.1
      exact ⟨owners, ⟨producer, payload, task⟩, ref, owner, announced⟩
    · intro before cut occurrence after split
      exact (witness before cut occurrence after split).2.2.2
  · rintro ⟨announced, uncancelled⟩ before cut occurrence after split
    have member : (cut, occurrence) ∈ failures := by simp [split]
    obtain ⟨bound, reachable, owners, producer, payload, task, failed⟩ :=
      inventory.2.2.1 _ member
    obtain ⟨otherOwners, ⟨parent, otherPayload, otherTask⟩, ref, owner, announcedRef⟩ :=
      announced _ member
    rw [← (task.unique otherTask).1] at owner
    refine ⟨bound, ?_, ⟨owners, producer, payload, task, failed, reachable,
      ref, owner, announcedRef⟩, uncancelled before cut occurrence after split⟩
    have ordered := inventory.1
    rw [split] at ordered
    intro earlier earlierMember
    exact (List.pairwise_append.mp ordered).2.2 earlier earlierMember
      _ List.mem_cons_self

/-- Merging eligible object candidates with supported stream cuts gives a complete inventory.
Witness: source-block provenance, unique source identities, ordered stream closures, and
both exact mixed-count theorems. No FailureWitness or admitted-output premise is used.
-/
theorem createWorkQueue_completeFailureInventory {work : Execution.Work}
    (generated : ExecutedWork work) {batches : List (List GraphEvent)}
    (valid : ValidGraphEvents work batches.flatten)
    (started : inputsStarted work batches = true) {streams : FailureCuts}
    (cuts
      : StreamFailureCuts work
          (((State.initialize (Work.fromExecution work)).runNormalized
              batches).2.flatten.flatMap
            publicationAtoms) streams)
    (reachable : ∀ entry ∈ streams, Reachable work entry.2)
    : let queue := State.initialize (Work.fromExecution work)
      let publisher : IncrementalPublisher :=
        { active := queue.initialGroups ++ queue.initialStreams }
      let objects :=
        sourceObjectFailureCuts 0
          (queue.eligibleFailureBlocks (queue.sourceRunBlocks publisher batches).2.2)
      CompleteFailureInventory work
        ((queue.runNormalized batches).2.flatten.flatMap publicationAtoms)
        (mergeFailureCuts objects streams) := by
  dsimp only
  let queue := State.initialize (Work.fromExecution work)
  let publisher : IncrementalPublisher :=
    { active := queue.initialGroups ++ queue.initialStreams }
  let objects := sourceObjectFailureCuts 0
    (queue.eligibleFailureBlocks (queue.sourceRunBlocks publisher batches).2.2)
  have origins := createWorkQueue_eligibleObjectFailureCuts_origin generated valid
  have objectKnown : ∀ entry ∈ objects,
      ∃ owners producer path errors,
        TaskAt work entry.2 owners producer (.object path (.error errors)) := by
    intro entry member
    obtain ⟨_, owners, producer, path, errors, task, _⟩ := origins entry member
    exact ⟨owners, producer, path, errors, task⟩
  have partition := mergeFailureCuts_partition objects streams
  refine ⟨
    mergeFailureCuts_ordered (sourceObjectFailureCuts_ordered _ _)
      (cuts.ordered.imp Nat.le_of_lt),
    cuts.mixed_unique (createWorkQueue_runNormalized_atomicStreamActions_ordered valid)
      (createWorkQueue_eligibleObjectFailureCuts_unique valid) objectKnown partition,
    ?_,
    ?_,
    ?_
  ⟩
  · intro entry member
    rcases List.mem_append.mp (partition.mem_iff.mp member) with fromStream | fromObject
    · obtain ⟨stream, errors, producer, _, task⟩ := cuts.2 entry fromStream
      exact ⟨Nat.le_of_lt (cuts.bound fromStream), reachable entry fromStream,
        [stream.ref], producer, _, task, rfl⟩
    · obtain ⟨bound, owners, producer, path, errors, task, reaches⟩ := origins entry fromObject
      exact ⟨bound, reaches, owners, producer, _, task, rfl⟩
  · intro index group errors atEvent
    exact createWorkQueue_mixedFailureCuts_groupNodeErrors generated valid started cuts
      partition atEvent
  · intro index stream errors atEvent
    exact createWorkQueue_mixedFailureCuts_streamNodeErrors generated valid cuts
      partition atEvent

/-- Every generated, valid, started replay has a complete ordered candidate failure list.
Witness: choose the already proved joint publication matching, label each stream failure,
and merge those cuts with guard-selected source object cuts. This proves finite inventory
existence only; causal licensing and scheduler conformance are still separate.
-/
theorem createWorkQueue_completeFailureInventory_exists {work : Execution.Work}
    (generated : ExecutedWork work) {batches : List (List GraphEvent)}
    (valid : ValidGraphEvents work batches.flatten)
    (started : inputsStarted work batches = true)
    : ∃ failures : FailureCuts,
        CompleteFailureInventory work
          (((State.initialize (Work.fromExecution work)).runNormalized
              batches).2.flatten.flatMap
            publicationAtoms) failures := by
  obtain ⟨matching, _, values, _, covered⟩ :=
    createWorkQueue_runNormalized_streamProducerMatching_withItemCoverage generated valid started
  obtain ⟨streams, cuts, _, supported⟩ := createWorkQueue_runNormalized_streamFailureCuts
    generated valid matching (fun index event atEvent value =>
      (values index event atEvent value).1) covered
  exact ⟨_, createWorkQueue_completeFailureInventory generated valid started cuts
    (fun entry member => (supported entry member).1)⟩

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
