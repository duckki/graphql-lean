import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.AcceptedFailureHealth
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.FailureAnnouncementCuts
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.AncestorGuardHealth
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RecordFailureRoles

/-! Direct-contributor safety under the single ordered mixed failure inventory. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Mixing stream cuts preserves the complete object-settlement order
-----------------------------------------------------------------------------------------

/-- Select execution-group cuts without inspecting queue state or failure counts. -/
private def objectCut (entry : Nat × Occurrence) : Bool :=
  match entry.2 with
  | .executionGroup _ => true
  | .item _ _ => false

/-- An object descriptor identifies an execution-group cut.
Witness: an item occurrence cannot have an object payload.
-/
private theorem objectCut_of_object {work cut occurrence owners producer path result}
    (known : TaskAt work occurrence owners producer (.object path result))
    : objectCut (cut, occurrence) = true := by
  cases occurrence with
  | executionGroup => rfl
  | item =>
      obtain ⟨_, _, _, _, _, _, _, _, impossible⟩ := known
      cases impossible

/-- An item descriptor cannot identify an execution-group cut.
Witness: an execution-group occurrence cannot have an item payload.
-/
private theorem objectCut_of_item {work cut occurrence owners producer stream result}
    (known : TaskAt work occurrence owners producer (.item stream result))
    : objectCut (cut, occurrence) = false := by
  cases occurrence with
  | item => rfl
  | executionGroup =>
      obtain ⟨_, _, _, _, _, _, _, impossible⟩ := known
      cases impossible

/-- Filtering a merge by disjoint input roles recovers the left list in its exact order.
Witness: follow either merge branch; right-hand entries are erased, not reordered.
-/
private theorem merge_filter_left (predicate : Nat × Occurrence → Bool)
    (objects streams : FailureCuts)
    (keep : ∀ entry ∈ objects, predicate entry = true)
    (drop : ∀ entry ∈ streams, predicate entry = false)
    : (mergeFailureCuts objects streams).filter predicate = objects := by
  induction objects generalizing streams with
  | nil =>
      simp only [mergeFailureCuts, List.nil_merge]
      apply List.filter_eq_nil_iff.mpr
      intro entry member
      simp [drop entry member]
  | cons entry rest ih =>
      induction streams with
      | nil =>
          simpa [mergeFailureCuts] using List.filter_eq_self.mpr keep
      | cons stream streams next =>
          unfold mergeFailureCuts
          rw [List.cons_merge_cons]
          split
          · simp only [List.filter_cons, keep entry List.mem_cons_self, ↓reduceIte]
            exact congrArg (entry :: ·)
              (ih _ (fun _ member => keep _ (List.mem_cons_of_mem _ member)) drop)
          · simp only [List.filter_cons, drop stream List.mem_cons_self, Bool.false_eq_true,
              ↓reduceIte]
            exact next (fun _ member => drop _ (List.mem_cons_of_mem _ member))

/-- A mixed object cut retains its exact object-settlement prefix, including equal cuts.
Witness: filter the stable merge by occurrence kind; item cuts disappear without moving
or reordering any object cut. Every earlier object cause remains in the recovered prefix.
-/
theorem mixedFailureCuts_objectPrefix
    {work events objects streams before after cut address}
    (objectsKnown
      : ∀ entry ∈ objects,
          ∃ owners producer path errors,
            TaskAt work entry.2 owners producer (.object path (.error errors)))
    (cuts : StreamFailureCuts work events streams)
    (split
      : mergeFailureCuts objects streams
        = before ++ (cut, .executionGroup address) :: after)
    : ∃ prior later,
        objects = prior ++ (cut, .executionGroup address) :: later
        ∧ ∀ entry ∈ before,
            ∀ owners producer path result,
              TaskAt work entry.2 owners producer (.object path result)
              → entry ∈ prior := by
  have filtered := merge_filter_left objectCut objects streams
    (fun entry member => by
      obtain ⟨_, _, _, _, known⟩ := objectsKnown entry member
      exact objectCut_of_object known)
    (fun entry member => by
      obtain ⟨_, _, _, _, known⟩ := cuts.2 entry member
      exact objectCut_of_item known)
  rw [split] at filtered
  simp only [List.filter_append, List.filter_cons, objectCut, ↓reduceIte] at filtered
  refine ⟨before.filter objectCut, after.filter objectCut, filtered.symm, ?_⟩
  intro entry member owners producer path result known
  exact List.mem_filter.mpr ⟨member, objectCut_of_object known⟩

/-- Stream-failure refs differ at any two distinct cuts in their ordered inventory.
Witness: strict cut ordering and the implementation's no-action-after-closure property.
-/
private theorem streamCut_refs_ne
    {work events streams first second left right leftErrors rightErrors}
    (cuts : StreamFailureCuts work events streams)
    (ordered : (events.filterMap streamAction).Pairwise StreamAction.Before)
    (firstMember : first ∈ streams) (secondMember : second ∈ streams)
    (different : first ≠ second)
    (atLeft : events[first.1]? = some (.streamFailure left leftErrors))
    (atRight : events[second.1]? = some (.streamFailure right rightErrors))
    : left.ref ≠ right.ref := by
  obtain ⟨i, hi, firstEq⟩ := List.mem_iff_getElem.mp firstMember
  obtain ⟨j, hj, secondEq⟩ := List.mem_iff_getElem.mp secondMember
  rcases Nat.lt_trichotomy i j with earlier | same | later
  · have before := cuts.ordered.rel_getElem_of_lt hi hj earlier
    rw [firstEq, secondEq] at before
    exact streamFailure_refs_ne ordered atLeft atRight before
  · subst j
    exact False.elim (different (firstEq.symm.trans secondEq))
  · have before := cuts.ordered.rel_getElem_of_lt hj hi later
    rw [firstEq, secondEq] at before
    exact Ne.symm (streamFailure_refs_ne ordered atRight atLeft before)

/-- An object task's contributing owner has a structural group descriptor.
Witness: its execution-group location contains exactly that owner descriptor.
-/
private theorem object_owner_group {work occurrence owners producer path result ref}
    (known : TaskAt work occurrence owners producer (.object path result))
    (contributes : ref ∈ owners)
    : ∃ node dependencies,
        NodeAt work node .group dependencies producer ∧ node.ref = ref := by
  cases occurrence with
  | item =>
      obtain ⟨_, _, _, _, _, _, _, _, impossible⟩ := known
      cases impossible
  | executionGroup address =>
      obtain ⟨groups, _, _, _, _, located, same, _⟩ := known
      rw [same] at contributes
      obtain ⟨group, member, refEq⟩ := List.mem_map.mp contributes
      exact ⟨group.node, group.ancestors.map Execution.DeliveryNode.ref,
        .group located member, refEq⟩

-----------------------------------------------------------------------------------------
-- One owner escapes all earlier direct failures, across both source kinds
-----------------------------------------------------------------------------------------

/-- Every accepted failure in the complete mixed inventory retains a direct-safe owner.
Witness: object cuts recover their unchanged ordered prefix by filtering the merge;
stream cuts use unique closure refs. Generated role separation excludes cross-kind
contributions. This does not yet exclude ancestor failure or producer cancellation.
-/
theorem createWorkQueue_mixedFailureCuts_directHealthyOwner {work : Execution.Work}
    (generated : ExecutedWork work) {batches : List (List GraphEvent)}
    (valid : ValidGraphEvents work batches.flatten)
    (started : inputsStarted work batches = true) {streams : FailureCuts}
    (cuts
      : StreamFailureCuts work
          (((State.initialize (Work.fromExecution work)).runNormalized
              batches).2.flatten.flatMap
            publicationAtoms) streams)
    {before after : FailureCuts} {cut : Nat} {occurrence : Occurrence}
    (split
      : let queue := State.initialize (Work.fromExecution work)
        let publisher : IncrementalPublisher :=
          { active := queue.initialGroups ++ queue.initialStreams }
        let objects :=
          sourceObjectFailureCuts 0
            (queue.eligibleFailureBlocks (queue.sourceRunBlocks publisher batches).2.2)
        mergeFailureCuts objects streams = before ++ (cut, occurrence) :: after)
    : ∃ owners owner,
        TaskHasOwners work occurrence owners
        ∧ owner ∈ owners
        ∧ ∀ prior priorOwners,
            prior ∈ before.map Prod.snd
            → TaskHasOwners work prior priorOwners
            → owner ∉ priorOwners := by
  let queue := State.initialize (Work.fromExecution work)
  let publisher : IncrementalPublisher :=
    { active := queue.initialGroups ++ queue.initialStreams }
  let objects := sourceObjectFailureCuts 0
    (queue.eligibleFailureBlocks (queue.sourceRunBlocks publisher batches).2.2)
  have objectKnown : ∀ entry ∈ objects,
      ∃ owners producer path errors,
        TaskAt work entry.2 owners producer (.object path (.error errors)) := by
    intro entry member
    obtain ⟨_, owners, producer, path, errors, known, _⟩ :=
      createWorkQueue_eligibleObjectFailureCuts_origin generated valid entry member
    exact ⟨owners, producer, path, errors, known⟩
  have partition := mergeFailureCuts_partition objects streams
  have current : (cut, occurrence) ∈ mergeFailureCuts objects streams := by
    rw [split]
    exact List.mem_append_right _ List.mem_cons_self
  have priorMember {entry} (member : entry ∈ before)
      : entry ∈ streams ∨ entry ∈ objects :=
    List.mem_append.mp (partition.mem_iff.mp (by
      rw [split]
      exact List.mem_append_left _ member))
  have ordered := createWorkQueue_runNormalized_atomicStreamActions_ordered valid
  have unique := cuts.mixed_unique ordered
    (createWorkQueue_eligibleObjectFailureCuts_unique valid) objectKnown partition
  have noPrior : occurrence ∉ before.map Prod.snd := by
    rw [split, List.map_append, List.map_cons, List.nodup_append] at unique
    intro member
    exact unique.2.2 occurrence member occurrence List.mem_cons_self rfl
  rcases List.mem_append.mp (partition.mem_iff.mp current) with fromStream | fromObject
  · obtain ⟨stream, errors, producer, atEvent, known⟩ := cuts.2 _ fromStream
    obtain ⟨_, dependencies, descriptor⟩ := itemTask_owner_nodeAt known
    refine ⟨[stream.ref], stream.ref, ⟨producer, _, known⟩, List.mem_cons_self, ?_⟩
    intro prior priorOwners member ⟨parent, payload, task⟩ contributes
    obtain ⟨entry, earlier, occurrenceEq⟩ := List.mem_map.mp member
    rcases priorMember earlier with otherStream | otherObject
    · obtain ⟨other, count, birth, atPrior, otherTask⟩ := cuts.2 entry otherStream
      rw [occurrenceEq] at otherTask
      have refs := (otherTask.unique task).1
      have equal : stream.ref = other.ref := List.mem_singleton.mp (refs.symm ▸ contributes)
      have different : entry ≠ (cut, occurrence) := by
        intro same
        apply noPrior
        exact List.mem_map.mpr ⟨entry, earlier, by rw [same]⟩
      exact streamCut_refs_ne cuts ordered otherStream fromStream different atPrior atEvent
        equal.symm
    · obtain ⟨owners, birth, path, count, object⟩ := objectKnown entry otherObject
      rw [occurrenceEq] at object
      exact generated.objectFailure_not_streamOwner descriptor object
        ((object.unique task).1.symm ▸ contributes)
  · obtain ⟨owners, producer, path, errors, task⟩ := objectKnown _ fromObject
    have filtered := merge_filter_left objectCut objects streams
      (fun entry member => by
        obtain ⟨_, _, _, _, task⟩ := objectKnown entry member
        exact objectCut_of_object task)
      (fun entry member => by
        obtain ⟨_, _, _, _, task⟩ := cuts.2 entry member
        exact objectCut_of_item task)
    rw [split] at filtered
    simp only [List.filter_append, List.filter_cons, objectCut_of_object task,
      ↓reduceIte] at filtered
    obtain ⟨owners, owner, ⟨birth, payload, descriptor⟩, contributes, safe⟩ :=
      createWorkQueue_eligibleObjectFailureCuts_directHealthyOwner generated valid started
        filtered.symm
    have ownersEq := (descriptor.unique task).1
    obtain ⟨group, dependencies, groupKnown, refEq⟩ :=
      object_owner_group task (ownersEq ▸ contributes)
    refine ⟨owners, owner, ⟨birth, payload, descriptor⟩, contributes, ?_⟩
    intro prior priorOwners member ⟨parent, value, priorTask⟩ owns
    obtain ⟨entry, earlier, occurrenceEq⟩ := List.mem_map.mp member
    rcases priorMember earlier with otherStream | otherObject
    · obtain ⟨stream, count, source, _, item⟩ := cuts.2 entry otherStream
      rw [occurrenceEq] at item
      exact generated.itemFailure_not_groupOwner groupKnown item
        (refEq.symm ▸ ((item.unique priorTask).1.symm ▸ owns))
    · obtain ⟨_, _, _, _, object⟩ := objectKnown entry otherObject
      exact safe prior priorOwners
        (List.mem_map.mpr ⟨entry, List.mem_filter.mpr ⟨earlier, objectCut_of_object object⟩,
          occurrenceEq⟩) ⟨parent, value, priorTask⟩ owns

-----------------------------------------------------------------------------------------
-- Stream cuts cannot add defer-ancestor cleanup causes to an accepted object cut
-----------------------------------------------------------------------------------------

/-- The same accepted object owner escapes cleanup invalidation in the full mixed prefix.
Witness: filtering the merge recovers its exact ordered object prefix; guard reflection
excludes that inventory, and generated defer roles exclude item failures from every
registration-ancestor cause. This is stronger than direct-contributor safety, but does
not yet exclude historical producer cancellation or license the stream cuts themselves.
-/
theorem createWorkQueue_mixedFailureCuts_uninvalidatedObjectOwner {work : Execution.Work}
    (generated : ExecutedWork work) {batches : List (List GraphEvent)}
    (valid : ValidGraphEvents work batches.flatten)
    (started : inputsStarted work batches = true)
    (missing
      : ∀ received : List GraphEvent,
          received.IsPrefix batches.flatten
          → State.MissingParentAncestorsHealthy
              ((State.initialize (Work.fromExecution work)).replayGraphEvents received)
              work
              ((State.initialize (Work.fromExecution work)).objectFailureContributions
                received))
    {streams : FailureCuts}
    (cuts
      : StreamFailureCuts work
          (((State.initialize (Work.fromExecution work)).runNormalized
              batches).2.flatten.flatMap
            publicationAtoms) streams)
    {before after : FailureCuts} {cut : Nat} {occurrence : Occurrence}
    {ownerRefs producer path result}
    (object : TaskAt work occurrence ownerRefs producer (.object path result))
    (split
      : let queue := State.initialize (Work.fromExecution work)
        let publisher : IncrementalPublisher :=
          { active := queue.initialGroups ++ queue.initialStreams }
        let objects :=
          sourceObjectFailureCuts 0
            (queue.eligibleFailureBlocks (queue.sourceRunBlocks publisher batches).2.2)
        mergeFailureCuts objects streams = before ++ (cut, occurrence) :: after)
    : ∃ owners ref,
        TaskHasOwners work occurrence owners
        ∧ ref ∈ owners
        ∧ ¬GroupRecordInvalidated work (before.map Prod.snd) ref := by
  let queue := State.initialize (Work.fromExecution work)
  let publisher : IncrementalPublisher :=
    { active := queue.initialGroups ++ queue.initialStreams }
  let objects := sourceObjectFailureCuts 0
    (queue.eligibleFailureBlocks (queue.sourceRunBlocks publisher batches).2.2)
  have filtered := merge_filter_left objectCut objects streams
    (fun entry member => by
      obtain ⟨_, _, _, _, _, task, _⟩ :=
        createWorkQueue_eligibleObjectFailureCuts_origin generated valid entry member
      exact objectCut_of_object task)
    (fun entry member => by
      obtain ⟨_, _, _, _, task⟩ := cuts.2 entry member
      exact objectCut_of_item task)
  rw [split] at filtered
  simp only [List.filter_append, List.filter_cons, objectCut_of_object object,
    ↓reduceIte] at filtered
  obtain ⟨owners, ref, ⟨birth, payload, task⟩, owner, safe⟩ :=
    createWorkQueue_eligibleObjectFailureCuts_uninvalidatedOwner
      generated valid started missing filtered.symm
  obtain ⟨group, dependencies, descriptor, same⟩ :=
    object_owner_group object ((task.unique object).1 ▸ owner)
  refine ⟨owners, ref, ⟨birth, payload, task⟩, owner, ?_⟩
  intro invalid
  have record := groupRecordAt_of_nodeAt descriptor
  apply safe
  rw [← same] at invalid ⊢
  apply invalid.restrict_objectFailures generated record
  intro prior priorOwners priorProducer priorPath priorResult known member
  obtain ⟨entry, earlier, equal⟩ := List.mem_map.mp member
  refine List.mem_map.mpr ⟨entry, List.mem_filter.mpr ⟨earlier, ?_⟩, equal⟩
  exact objectCut_of_object (equal.symm ▸ known)

-----------------------------------------------------------------------------------------
-- Preserve counts, announcements, and direct safety under the same chosen inventory
-----------------------------------------------------------------------------------------

/-- Actual replay has one complete announced inventory with direct-safe owners at all cuts.
Witness: merge the original object cuts and actual stream cuts once, then attach all
three certificates to that same list. Announcement and health may use different owners;
this still leaves ancestor failure and producer cancellation to the conformance proof.
-/
theorem createWorkQueue_failureInventory_withDirectSafety {work : Execution.Work}
    (generated : ExecutedWork work) {batches : List (List GraphEvent)}
    (valid : ValidGraphEvents work batches.flatten)
    (started : inputsStarted work batches = true)
    : let queue := State.initialize (Work.fromExecution work)
      let atoms := (queue.runNormalized batches).2.flatten.flatMap publicationAtoms
      let initial :=
        (queue.initialGroups ++ queue.initialStreams).map Execution.DeliveryNode.ref
      ∃ failures : FailureCuts,
        CompleteFailureInventory work atoms failures
        ∧ (∀ entry ∈ failures,
            ∃ owners,
              TaskHasOwners work entry.2 owners
              ∧ ∃ ref ∈ owners, ref ∈ announcedRefs initial (atoms.take entry.1))
        ∧ ∀ before cut occurrence after,
            failures = before ++ (cut, occurrence) :: after
            → ∃ owners owner,
                TaskHasOwners work occurrence owners
                ∧ owner ∈ owners
                ∧ ∀ prior priorOwners,
                    prior ∈ before.map Prod.snd
                    → TaskHasOwners work prior priorOwners
                    → owner ∉ priorOwners := by
  dsimp only
  let queue := State.initialize (Work.fromExecution work)
  let publisher : IncrementalPublisher :=
    { active := queue.initialGroups ++ queue.initialStreams }
  let objects := sourceObjectFailureCuts 0
    (queue.eligibleFailureBlocks (queue.sourceRunBlocks publisher batches).2.2)
  obtain ⟨matching, _, values, _, covered⟩ :=
    createWorkQueue_runNormalized_streamProducerMatching_withItemCoverage generated valid started
  obtain ⟨streams, cuts, _, supported⟩ := createWorkQueue_runNormalized_streamFailureCuts
    generated valid matching (fun index event atEvent value =>
      (values index event atEvent value).1) covered
  refine ⟨mergeFailureCuts objects streams,
    createWorkQueue_completeFailureInventory generated valid started cuts
      (fun entry member => (supported entry member).1), ?_, ?_⟩
  · intro entry member
    rcases List.mem_append.mp ((mergeFailureCuts_partition objects streams).mem_iff.mp member)
        with fromStream | fromObject
    · obtain ⟨ref, owners, opened⟩ := (supported entry fromStream).2.2
      exact ⟨[ref], owners, ref, List.mem_cons_self, opened.1⟩
    · obtain ⟨before, after, split⟩ := List.mem_iff_append.mp fromObject
      obtain ⟨owners, ref, structural, contributes, announced⟩ :=
        createWorkQueue_eligibleObjectFailureCuts_announcedOwner valid started split
      exact ⟨owners, structural, ref, contributes, announced⟩
  · intro before cut occurrence after split
    exact createWorkQueue_mixedFailureCuts_directHealthyOwner generated valid started cuts split

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
