import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.SelectedGroupFailureInventory
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.AcceptedFailureHealth
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.FailureAnnouncementCuts

/-! Informative source cuts preserve causal invalidation and prior announcement evidence. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Proof-side source cut selection; actual inputs and output positions are unchanged. -/
noncomputable def informativeObjectFailureCuts (work : Execution.Work)
    (blocks : List SourceOutputBlock)
    : FailureCuts :=
  selectObjectFailureCuts work [] (availableObjectFailureCuts work 0 blocks)

/-- Informative object cuts retain their original candidate positions and source order. -/
theorem informativeObjectFailureCuts_sublist (work : Execution.Work)
    (blocks : List SourceOutputBlock)
    : (informativeObjectFailureCuts work blocks).Sublist
        (availableObjectFailureCuts work 0 blocks) :=
  selectObjectFailureCuts_sublist work [] _

/-- Every selected cause visible at a boundary was a visible original candidate there. -/
theorem informativeObjectFailureCuts_failedBefore_subset (work : Execution.Work)
    (blocks : List SourceOutputBlock) (bound : Nat)
    : (failedBefore (informativeObjectFailureCuts work blocks) bound).Subset
        (failedBefore (availableObjectFailureCuts work 0 blocks) bound) := by
  intro occurrence member
  obtain ⟨entry, selected, same⟩ := List.mem_map.mp member
  exact List.mem_map.mpr ⟨entry, List.mem_filter.mpr
    ⟨(informativeObjectFailureCuts_sublist work blocks).subset (List.mem_filter.mp selected).1,
      (List.mem_filter.mp selected).2⟩, same⟩

/-- Informative object cuts retain nondecreasing output positions. -/
theorem informativeObjectFailureCuts_ordered (work : Execution.Work)
    (blocks : List SourceOutputBlock)
    : (informativeObjectFailureCuts work blocks).Pairwise
        (fun left right => left.1 ≤ right.1) :=
  (availableObjectFailureCuts_ordered work 0 blocks).sublist
    (informativeObjectFailureCuts_sublist work blocks)

/-- Selected candidates retain fixed failed-task provenance, bounds, and reachability. -/
theorem createWorkQueue_informativeObjectFailureCuts_origin {work : Execution.Work}
    {batches : List (List GraphEvent)} (generated : ExecutedWork work)
    (valid : ValidGraphEvents work batches.flatten)
    : let queue := State.initialize (Work.fromExecution work)
      let publisher : IncrementalPublisher :=
        { active := queue.initialGroups ++ queue.initialStreams }
      let blocks := (queue.sourceRunBlocks publisher batches).2.2
      ∀ entry ∈ informativeObjectFailureCuts work blocks,
        entry.1
          ≤ ((queue.runNormalized batches).2.flatten.flatMap publicationAtoms).length
        ∧ ∃ owners producer path errors,
            TaskAt work entry.2 owners producer (.object path (.error errors))
            ∧ Reachable work entry.2 := by
  dsimp only
  intro entry member
  exact createWorkQueue_availableObjectFailureCuts_origin generated valid entry
    ((informativeObjectFailureCuts_sublist work _).subset member)

/-- Source freshness also excludes repeated selected failure occurrences. -/
theorem createWorkQueue_informativeObjectFailureCuts_unique {work : Execution.Work}
    {batches : List (List GraphEvent)} (_valid : ValidGraphEvents work batches.flatten)
    : let queue := State.initialize (Work.fromExecution work)
      let publisher : IncrementalPublisher :=
        { active := queue.initialGroups ++ queue.initialStreams }
      let blocks := (queue.sourceRunBlocks publisher batches).2.2
      ((informativeObjectFailureCuts work blocks).map Prod.snd).Nodup := by
  dsimp only
  exact (availableObjectFailureCuts_unique _ _ _).sublist
    ((informativeObjectFailureCuts_sublist work _).map Prod.snd)

/-- A selected cut retains the same previously announced contributor as its source cut. -/
theorem createWorkQueue_informativeObjectFailureCuts_announcedOwner
    {work : Execution.Work} (generated : ExecutedWork work)
    {batches : List (List GraphEvent)} (valid : ValidGraphEvents work batches.flatten)
    (started : inputsStarted work batches = true) {before after : FailureCuts} {cut : Nat}
    {occurrence : Occurrence}
    (split
      : let queue := State.initialize (Work.fromExecution work)
        let publisher : IncrementalPublisher :=
          { active := queue.initialGroups ++ queue.initialStreams }
        informativeObjectFailureCuts work ((queue.sourceRunBlocks publisher batches).2.2)
        = before ++ (cut, occurrence) :: after)
    : let queue := State.initialize (Work.fromExecution work)
      ∃ owners owner,
        TaskHasOwners work occurrence owners
        ∧ owner ∈ owners
        ∧ owner
          ∈ announcedRefs
              ((queue.initialGroups ++ queue.initialStreams).map
                Execution.DeliveryNode.ref)
              (((queue.runNormalized batches).2.flatten.flatMap publicationAtoms).take
                cut) := by
  let queue := State.initialize (Work.fromExecution work)
  let publisher : IncrementalPublisher := { active := queue.initialGroups ++ queue.initialStreams }
  have member : (cut, occurrence) ∈ informativeObjectFailureCuts work
      ((queue.sourceRunBlocks publisher batches).2.2) := by
    rw [split]
    exact List.mem_append_right _ List.mem_cons_self
  have raw := (informativeObjectFailureCuts_sublist work _).subset member
  exact createWorkQueue_availableObjectFailureCuts_announcedOwner generated valid started
    raw

/-- Every selected object cut has a direct-safe contributor at its exact selected prefix. -/
theorem informativeObjectFailureCuts_directHealthyOwner
    {work blocks before after cut occurrence}
    (split
      : informativeObjectFailureCuts work blocks = before ++ (cut, occurrence) :: after)
    : ∃ owners owner,
        TaskHasOwners work occurrence owners
        ∧ owner ∈ owners
        ∧ ∀ prior priorOwners,
            prior ∈ before.map Prod.snd
            → TaskHasOwners work prior priorOwners
            → owner ∉ priorOwners := by
  have selected := selectObjectFailureCuts_informative work [] (availableObjectFailureCuts work 0 blocks)
  rw [show selectObjectFailureCuts work [] (availableObjectFailureCuts work 0 blocks)
    = before ++ (cut, occurrence) :: after from split] at selected
  exact informativeFailureCuts_directHealthyOwner selected

/-- An object owner's structural descriptor supplies its group node. -/
theorem TaskAt.objectOwner_groupNode {work occurrence owners producer path result ref}
    (known : TaskAt work occurrence owners producer (.object path result))
    (owner : ref ∈ owners)
    : ∃ node dependencies,
        NodeAt work node .group dependencies producer ∧ node.ref = ref := by
  cases occurrence with
  | executionGroup address =>
      obtain ⟨groups, _, _, _, _, located, same, _⟩ := known
      rw [same] at owner
      obtain ⟨group, member, refEq⟩ := List.mem_map.mp owner
      exact ⟨group.node, group.ancestors.map Execution.DeliveryNode.ref,
        .group located member, refEq⟩
  | item =>
      obtain ⟨_, _, _, _, _, _, _, _, impossible⟩ := known
      cases impossible

/-- A selected object cut has an owner unaffected by earlier record invalidation. -/
theorem informativeObjectCuts_uninvalidatedOwner
    {work objects before after cut occurrence owners producer path result}
    (generated : ExecutedWork work)
    (object : TaskAt work occurrence owners producer (.object path result))
    (informative : InformativeFailureCuts work [] objects)
    (split : objects = before ++ (cut, occurrence) :: after)
    : ∃ contributors ref,
        TaskHasOwners work occurrence contributors
        ∧ ref ∈ contributors
        ∧ ¬GroupRecordInvalidated work (before.map Prod.snd) ref := by
  rw [split] at informative
  obtain ⟨contributors, ref, ⟨birth, payload, task⟩, owner, healthy⟩ := informative.atCut
  obtain ⟨node, dependencies, known, same⟩ :=
    TaskAt.objectOwner_groupNode object ((task.unique object).1 ▸ owner)
  refine ⟨contributors, ref, ⟨birth, payload, task⟩, owner, ?_⟩
  intro invalid
  exact healthy (same ▸ (generated.groupRecordInvalidated_iff_groupInvalidated known).mp
    (same.symm ▸ invalid))

/-- The ordinary source-block inventory specializes structural selection. -/
theorem informativeObjectFailureCuts_uninvalidatedOwner
    {work blocks before after cut occurrence owners producer path result}
    (generated : ExecutedWork work)
    (object : TaskAt work occurrence owners producer (.object path result))
    (split
      : informativeObjectFailureCuts work blocks = before ++ (cut, occurrence) :: after)
    : ∃ contributors ref,
        TaskHasOwners work occurrence contributors
        ∧ ref ∈ contributors
        ∧ ¬GroupRecordInvalidated work (before.map Prod.snd) ref :=
  informativeObjectCuts_uninvalidatedOwner generated object
    (selectObjectFailureCuts_informative work [] _) split

/-- Informative object cuts and stream failures form a causal inventory.
Witness: selection preserves group invalidation while stream roles retain their individual
causes. Aggregate group totals belong to the separate reporting inventory.
-/
theorem createWorkQueue_completeInformativeFailureInventory {work : Execution.Work}
    (generated : ExecutedWork work) {batches : List (List GraphEvent)}
    (valid : ValidGraphEvents work batches.flatten)
    {streams : FailureCuts}
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
        informativeObjectFailureCuts work ((queue.sourceRunBlocks publisher batches).2.2)
      CausalFailureInventory work
        ((queue.runNormalized batches).2.flatten.flatMap publicationAtoms)
        (mergeFailureCuts objects streams) := by
  dsimp only
  let queue := State.initialize (Work.fromExecution work)
  let publisher : IncrementalPublisher :=
    { active := queue.initialGroups ++ queue.initialStreams }
  let objects := informativeObjectFailureCuts work
    ((queue.sourceRunBlocks publisher batches).2.2)
  have origins := createWorkQueue_informativeObjectFailureCuts_origin generated valid
  have objectKnown : ∀ entry ∈ objects,
      ∃ owners producer path errors,
        TaskAt work entry.2 owners producer (.object path (.error errors)) := by
    intro entry member
    obtain ⟨_, owners, producer, path, errors, task, _⟩ := origins entry member
    exact ⟨owners, producer, path, errors, task⟩
  have partition := mergeFailureCuts_partition objects streams
  refine ⟨
    mergeFailureCuts_ordered (informativeObjectFailureCuts_ordered _ _)
      (cuts.ordered.imp Nat.le_of_lt),
    cuts.mixed_unique (createWorkQueue_runNormalized_atomicStreamActions_ordered valid)
      (createWorkQueue_informativeObjectFailureCuts_unique valid) objectKnown partition,
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
    apply (createWorkQueue_selectedObjectFailureCuts_groupInvalidated generated valid atEvent).mono
    intro occurrence member
    exact (failedBefore_partition partition index).mem_iff.mpr
      (List.mem_append_right _ member)
  · intro index stream errors atEvent
    apply cuts.nodeErrors_mixed partition objectKnown generated
      (createWorkQueue_runNormalized_atomicStreamActions_ordered valid) atEvent

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
