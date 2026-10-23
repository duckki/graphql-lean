import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ObjectFailureCuts

/-! Cached report causes use the failed group's previously announced contributor. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Every aggregate-report candidate has an owner announced before its exact report cut.
The stored failed group is a contributor of each selected source rejection. Its existing
notice supplies the license even when that rejection's FIFO callback has not run. -/
theorem createWorkQueue_groupReportCandidateCuts_announcedOwner {work : Execution.Work}
    (generated : ExecutedWork work) {batches : List (List GraphEvent)}
    (valid : ValidGraphEvents work batches.flatten) {entry : Nat × Occurrence}
    (member
      : let queue := State.initialize (Work.fromExecution work)
        let publisher : IncrementalPublisher :=
          { active := queue.initialGroups ++ queue.initialStreams }
        let blocks := (queue.sourceRunBlocks publisher batches).2.2
        entry
        ∈ groupReportCandidateCuts work (blocks.filterMap Prod.fst) 0
            (blocks.flatMap Prod.snd))
    : let queue := State.initialize (Work.fromExecution work)
      ∃ owners owner,
        TaskHasOwners work entry.2 owners
        ∧ owner ∈ owners
        ∧ owner
          ∈ announcedRefs
              ((queue.initialGroups ++ queue.initialStreams).map
                Execution.DeliveryNode.ref)
              (((queue.runNormalized batches).2.flatten.flatMap publicationAtoms).take
                entry.1) := by
  dsimp only at member ⊢
  obtain ⟨index, group, errors, count, selected, cut, cause⟩ :=
    groupReportCandidateCuts_origin member
  have totals := createWorkQueue_sourceRunBlocks_groupFailureTotals generated valid
  have sources := totals group errors (List.mem_of_getElem? selected)
  simp only [List.nil_append] at sources
  obtain ⟨_, owners, producer, path, known, owner⟩ :=
    (groupReportSourceParts_spec sources).2.2.2 entry.2 count cause
  refine ⟨owners, group.ref, ⟨producer, _, known⟩, owner, ?_⟩
  have actual := selected
  rw [(State.sourceRunBlocks_agrees _ _).2] at actual
  have announced := createWorkQueue_runNormalized_groupFailureAnnouncedAt valid actual
  simpa only [cut, Nat.zero_add] using announced

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
