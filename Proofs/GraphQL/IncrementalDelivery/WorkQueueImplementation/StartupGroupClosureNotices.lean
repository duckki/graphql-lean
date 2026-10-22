import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.InitialStartupReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.InitialStartupAnnouncements
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.InitialStartupReportingAvailability
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupPublicationLedger
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupClosureNotices

/-! Actual startup group completions retain their strictly prior announcements. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Every active or queued startup group retains its original initial announcement. -/
theorem State.initializeWithStartup_groupNoticeSupport (work : Execution.Work)
    (startup : InitialStartup)
    : let queue := State.initialize (Work.fromExecution work) startup
      queue.groupNoticeSupport.Subset
        (queue.initialGroups.map Execution.DeliveryNode.ref) := by
  dsimp only
  intro ref member
  rcases List.mem_append.mp member with active | waiting
  · exact (State.initializeWithStartup_announcementFacts work startup).roots active
  · obtain ⟨failure, queued, same⟩ := List.mem_map.mp waiting
    exact same ▸ State.initializeWithStartup_failure_refs (Work.fromExecution work) startup
      failure queued

/-- Actual startup group closures follow initial or earlier emitted group notices.
Both active roots and pending control descriptors participate in the same notice ledger. -/
theorem State.startup_runNormalized_groupClosureNotices {work : Execution.Work}
    (startup : InitialStartup) {batches : List (List GraphEvent)}
    (_valid : ValidGraphEvents work batches.flatten)
    : let initial := State.initialize (Work.fromExecution work) startup
      ReferencesAnnounced groupNoticeRefs groupClosureRefs
        (initial.initialGroups.map Execution.DeliveryNode.ref)
        (initial.runNormalized batches).2.flatten := by
  let initial := State.initialize (Work.fromExecution work) startup
  let refs := initial.initialGroups.map Execution.DeliveryNode.ref
  have loop (more : List (List GraphEvent)) (acc : NormalizedAcc)
      (roots : acc.1.groupNoticeSupport.Subset (refs ++ acc.2.2.flatten.flatMap groupNoticeRefs))
      (known : ReferencesAnnounced groupNoticeRefs groupClosureRefs refs acc.2.2.flatten)
      : ReferencesAnnounced groupNoticeRefs groupClosureRefs refs
          (more.foldl normalizedStep acc).2.2.flatten := by
    induction more generalizing acc with
    | nil => exact known
    | cons batch rest ih =>
        have localFacts := acc.1.handleGraphEvents_fifoGroupFailureNotices batch
        apply ih
        · rw [normalizedStep_queue, normalizedStep_flatten, List.flatMap_append,
            IncrementalPublisher.normalizeBatch_groupNotices]
          intro ref member
          rcases List.mem_append.mp (localFacts.known member) with old | added
          · exact (List.mem_append.mp (roots old)).elim
              (fun root => List.mem_append_left _ root)
              (fun prior => List.mem_append_right _ (List.mem_append_left _ prior))
          · exact List.mem_append_right _ (List.mem_append_right _ added)
        · rw [normalizedStep_flatten]
          exact known.append
            (((acc.1.handleGraphEvents_closureNotices batch).normalizeGroupClosures acc.2.1).mono
              roots)
  let publisher : IncrementalPublisher :=
    { active := initial.initialGroups ++ initial.initialStreams }
  exact loop batches (initial, publisher, [])
    (by
      simpa only [List.flatten_nil, List.flatMap_nil, List.append_nil]
        using State.initializeWithStartup_groupNoticeSupport work startup) trivial

/-- Every actual atomic startup group completion has an earlier contributing notice. -/
theorem State.startup_runNormalized_groupClosureAnnouncedAt {work : Execution.Work}
    (startup : InitialStartup) {batches : List (List GraphEvent)}
    (valid : ValidGraphEvents work batches.flatten) {index : Nat} {event ref}
    (selected
      : let initial := State.initialize (Work.fromExecution work) startup
        ((initial.runNormalized batches).2.flatten.flatMap publicationAtoms)[index]?
        = some event)
    (closed : ref ∈ groupClosureRefs event)
    : let initial := State.initialize (Work.fromExecution work) startup
      ref
      ∈ announcedRefs
          ((initial.initialGroups ++ initial.initialStreams).map
            Execution.DeliveryNode.ref)
          (((initial.runNormalized batches).2.flatten.flatMap publicationAtoms).take
            index) := by
  have known := ((State.startup_runNormalized_groupClosureNotices startup valid).groupClosureAtoms
    (State.runNormalized_nonemptyValues _ _ valid.nonemptyItems).2).atEvent selected closed
  rcases List.mem_append.mp known with initial | prior
  · apply List.mem_append_left
    rw [List.map_append]
    exact List.mem_append_left _ initial
  · apply List.mem_append_right
    obtain ⟨carrier, member, noticed⟩ := List.mem_flatMap.mp prior
    apply List.mem_flatMap.mpr ⟨carrier, member, ?_⟩
    cases carrier <;> simp_all [groupNoticeRefs, eventPending, List.map_append]

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
