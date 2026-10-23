import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.AvailableRegistrationFrame
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.AvailableTaskSuccessProgress
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.AvailableStreamTaskProgress
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.FusedTaskFailureProgress

/-! All-handler unfinished-task progress at an exposed source cut. Snapshot stability is
derived by cache idempotence at actual FIFO cuts, not imposed on host event sources.
-/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
open WorkQueueSemantics (Occurrence NodeRefs)
open GraphQL.IncrementalDelivery.Execution (DeliveryNode)

private theorem taskRepresented {queue : ReferenceWorkQueue.State}
    {task : ReferenceWorkQueue.Task}
    (links : queue.TaskLinkedOn task.occurrence (task.groups.map DeliveryNode.ref))
    (owned : ∃ owner ∈ task.groups, ∃ group, queue.groupNode? owner.ref = some group)
    (prior : queue.TaskRejectionsSatisfy (fun rejected _ => rejected ≠ task.occurrence))
    : RecordTargetRepresented queue (.task task.occurrence) := by
  obtain ⟨owner, member, group, found⟩ := owned
  exact .task found (links group (List.mem_of_find?_eq_some found)
    (List.mem_map.mpr ⟨owner, member, (ReferenceWorkQueue.State.groupNode?_ref found).symm⟩))
      prior.unrejected_lookup

/-- Every prepared unfinished task with a live owner has a real endpoint record or an
abort in the actual dispatch. All five handlers retain the supplied failure snapshot.
-/
theorem sourceFrame_preparedTask_progress_available {queue : ReferenceWorkQueue.State}
    {work parents before event task} (generated : ReferenceWorkQueue.ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          ReferenceWorkQueue.GroupRecordAt work node dependencies
          → dependencies = parents node.ref)
    (source : ReferenceWorkQueue.UncancelledReplayFrame queue work parents before)
    (accounted
      : queue.PendingAccounting work
          (ReferenceWorkQueue.GraphEvent.taskSettlements before))
    (keys : queue.TaskNodeKeysUnique)
    (valid : ReferenceWorkQueue.ValidGraphEvents work (before ++ [event]))
    (available : List (Occurrence × Nat))
    (cached : queue.cacheTaskFailures available = queue)
    (unrejected
      : queue.TaskRejectionsSatisfy (fun rejected _ => rejected ≠ task.occurrence))
    (licensed
      : ∀ occurrence errors,
          (occurrence, errors) ∈ available → occurrence ≠ task.occurrence)
    (registered : task ∈ (registrationSnapshot queue event available).tasks)
    (pending
      : task.occurrence
        ∉ event.recordTaskOutcome (ReferenceWorkQueue.GraphEvent.taskSettlements before))
    (owned
      : ∃ owner ∈ task.groups,
          ∃ group,
            (registrationSnapshot queue event available).groupNode? owner.ref
            = some group)
    : let reduced := ({ queue } : State).handleGraphEvent event available
      RecordTargetRepresented reduced.1.queue (.task task.occurrence)
      ∨ .abortTask task.occurrence ∈ reduced.2.2.1 := by
  obtain ⟨prior, matched, fresh⟩ := ReferenceWorkQueue.validGraphEvents_last valid
  have notSettled
      : task.occurrence ∉ ReferenceWorkQueue.GraphEvent.taskSettlements before := by
    intro member
    apply pending
    cases event with
    | taskSuccess | taskFailure => exact List.mem_cons_of_mem _ member
    | streamItems | groupFailure | streamSuccess | streamFailure => exact member
  have registration := registrationSnapshot_frame_available
    (SourceRegistrationFrame.of_pendingAccounting accounted) accounted.registration event matched available
  have links := registration.links task registered notSettled
  have catalogue := registration.catalogue registered
  dsimp only
  cases event with
  | taskSuccess incoming result =>
      cases found : queue.taskNode? incoming with
      | none =>
          simp only [registrationSnapshot, found] at links owned
          simp only [State.handleGraphEvent, cached, State.taskSuccess, found]
          exact .inl (taskRepresented links owned unrejected)
      | some input =>
          have inputFresh : incoming ∉ ReferenceWorkQueue.GraphEvent.taskSettlements before := by
            intro member
            exact fresh.2.2.1 incoming List.mem_cons_self
              (ReferenceWorkQueue.GraphEvent.taskSettlements_subsetIdentities before member)
          have known : ∀ task ∈ result.work.tasks, ReferenceWorkQueue.TaskMatches work task := by
            intro task member
            obtain ⟨address, payload, same, located⟩ := matched.childTask_producer member
            exact ⟨⟨address, payload, some incoming, same, located⟩,
              matched.childTask_groupsExact member⟩
          have childFresh : ∀ task ∈ result.work.tasks,
              task.occurrence ∉ incoming :: ReferenceWorkQueue.GraphEvent.taskSettlements
                before := by
            intro task member used
            rcases List.mem_cons.mp used with now | earlier
            · exact matched.childTasks_not_success member (List.mem_cons.mpr (.inl now))
            · exact matched.childTasks_unsettled prior fresh member
                (ReferenceWorkQueue.GraphEvent.taskSettlements_subsetIdentities before earlier)
          have startup := taskSuccess_startFrames generated accounted.registration canonical source.roots.live
            source.roots.retired source.tasks source.parent.children incoming result
            matched input found
          have projection := snapshotProjection_of_structuralFrames generated canonical
            source.roots.live source.roots.retired source.tasks source.parent.children keys
            (.taskSuccess incoming result) matched
          have evidence := SnapshotTaskEvidence.of_projection projection
            (eagerRegistrationSnapshot_taskEvidence accounted
              (storedTaskLinks_of_taskOwnerFrame source.tasks)
              (fun _ member => ReferenceWorkQueue.GraphEvent.taskSettlements_subsetIdentities
                before member) (.taskSuccess incoming result) matched fresh)
          simp only [State.handleGraphEvent, cached]
          exact State.taskSuccess_preparedTask_progress_available (state := { queue })
            generated source.roots.live.present accounted keys incoming result input found
            inputFresh known childFresh rfl available ⟨parents, startup⟩ task pending
            unrejected licensed evidence catalogue links owned
  | streamItems stream items =>
      cases active : queue.rootStreams.contains stream.ref with
      | false =>
          simp only [registrationSnapshot, active, Bool.false_eq_true, ↓reduceIte] at links owned
          simp only [State.handleGraphEvent, cached, State.streamItems, active, Bool.not_false,
            ↓reduceIte]
          exact .inl (taskRepresented links owned unrejected)
      | true =>
          have known : ∀ item ∈ items, ∀ task ∈ item.work.tasks,
              ReferenceWorkQueue.TaskMatches work task := by
            intro item member task supplied
            obtain ⟨address, payload, same, located⟩ :=
              matched.streamItem_childTask_producer member supplied
            exact ⟨⟨address, payload, some item.occurrence, same, located⟩,
              matched.streamItem_childTask_groupsExact member supplied⟩
          have frames := streamItems_cacheFrames_of_structural generated canonical
            source.roots.live source.roots.retired source.tasks source.parent.children keys
            stream items matched available
          have drainFrames := streamItems_drainFrames generated canonical source.roots.live
            source.roots.retired source.tasks source.parent.children stream items matched available
          simp only [registrationSnapshot, active, ↓reduceIte] at catalogue links owned
          simp only [State.handleGraphEvent, cached]
          exact State.streamItems_preparedTask_progress_available (state := { queue })
            keys stream items known accounted matched rfl active available frames
            ⟨parents, drainFrames⟩ task pending unrejected licensed catalogue links owned
  | taskFailure failed errors =>
      have forest := ReferenceWorkQueue.State.RemovalForest.of_generated generated
        source.parent.children source.parent.links source.parent.records canonical
      have different : task.occurrence ≠ failed := fun same => pending (same ▸ List.mem_cons_self)
      have result := State.taskFailure_unsettledTask (state := { queue }) source.tasks forest
        failed errors task different catalogue links owned unrejected
      simp only [State.handleGraphEvent, cached]
      simpa only [State.handleGraphEvent, ReferenceWorkQueue.State.cacheTaskFailures,
        List.foldl_nil] using result
  | groupFailure failure =>
      simp only [registrationSnapshot] at links owned
      simp only [State.handleGraphEvent]
      rw [cached]
      simp only [ReferenceWorkQueue.State.handleGraphEvent,
        ReferenceWorkQueue.State.cacheTaskFailures, List.foldl_nil,
        ReferenceWorkQueue.State.groupFailure]
      split
      · exact .inl (taskRepresented links owned unrejected)
      · split <;> exact .inl (taskRepresented links owned unrejected)
  | streamSuccess stream =>
      simp only [registrationSnapshot] at links owned
      simp only [State.handleGraphEvent, cached]
      cases active : queue.rootStreams.contains stream.ref <;>
        simp only [ReferenceWorkQueue.State.handleGraphEvent,
          ReferenceWorkQueue.State.cacheTaskFailures, List.foldl_nil,
          ReferenceWorkQueue.State.streamSuccess, active, Bool.false_eq_true, ↓reduceIte] <;>
        exact .inl (taskRepresented links owned unrejected)

  | streamFailure stream errors =>
      simp only [registrationSnapshot] at links owned
      simp only [State.handleGraphEvent, cached]
      cases active : queue.rootStreams.contains stream.ref <;>
        simp only [ReferenceWorkQueue.State.handleGraphEvent,
          ReferenceWorkQueue.State.cacheTaskFailures, List.foldl_nil,
          ReferenceWorkQueue.State.streamFailure, active, Bool.false_eq_true, ↓reduceIte] <;>
        exact .inl (taskRepresented links owned unrejected)

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
