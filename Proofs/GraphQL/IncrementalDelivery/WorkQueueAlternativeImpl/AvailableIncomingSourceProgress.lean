import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.AdoptedSourceRecords

/-! Structural source adoption at actual cache-exposed FIFO cuts. -/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
open WorkQueueSemantics (Occurrence NodeAt)

/-- An adopted structural source acquires an actual record or that dispatch cancels it.
Registration provenance excludes collisions using only previously consumed inputs.
-/
theorem sourceFrame_adoptedSource_progress_available {queue : ReferenceWorkQueue.State}
    {work parents before event producer child dependencies}
    (generated : ReferenceWorkQueue.ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          ReferenceWorkQueue.GroupRecordAt work node dependencies
          → dependencies = parents node.ref)
    (source : ReferenceWorkQueue.UncancelledReplayFrame queue work parents before)
    (keys : queue.TaskNodeKeysUnique) (inventory : queue.ChildStreamInventory)
    (origins
      : queue.StreamsSatisfy
          (ReferenceWorkQueue.StreamProducerSeen work
            (before.flatMap (fun event => event.identities.1))))
    (valid : ReferenceWorkQueue.ValidGraphEvents work (before ++ [event]))
    (available : List (Occurrence × Nat))
    (cached : queue.cacheTaskFailures available = queue)
    (adopted : .adopt producer ∈ graphEffects queue event)
    (known : NodeAt work child .stream dependencies (some producer))
    : let reduced := ({ queue } : State).handleGraphEvent event available
      RecordTargetRepresented reduced.1.queue (.stream child.ref)
      ∨ .cancelSource child.ref ∈ reduced.2.2.1 := by
  dsimp only
  obtain ⟨prior, matching, fresh⟩ := ReferenceWorkQueue.validGraphEvents_last valid
  cases event with
  | taskSuccess incoming result =>
      cases inputFound : queue.taskNode? incoming with
      | none => simp [graphEffects, inputFound] at adopted
      | some input =>
          have same : producer = incoming := by
            simpa only [graphEffects, inputFound, List.mem_singleton,
              HostEffect.adopt.injEq]
              using adopted
          subst producer
          have absent := origins.freshProducer_streamAbsent generated known
            (fresh.2.2.1 incoming List.mem_cons_self)
          obtain ⟨node, found, _, value, held⟩ :=
            ReferenceWorkQueue.State.maybeIntegrateWork_fresh_stream_attached
              (ReferenceWorkQueue.State.putTaskNode_value_lookup inputFound result.value)
              result.work (matching.taskChildStreams_complete known) absent
          have projection := snapshotProjection_of_structuralFrames generated canonical
            source.roots.live source.roots.retired source.tasks source.parent.children keys
            (.taskSuccess incoming result) matching
          have prepared : (registrationSnapshot queue (.taskSuccess incoming result)
              available).taskNode? incoming = some node := by
            apply projection.buffered
            · simpa only [eagerRegistrationSnapshot, inputFound] using found
            · rw [value]; rfl
          exact sourceFrame_preparedSource_progress_available generated canonical source
            keys inventory valid trivial available cached
            (.bufferedStream prepared (by rw [value]; rfl) held)
  | streamItems stream items =>
      cases active : queue.rootStreams.contains stream.ref with
      | false => simp only [graphEffects, active, Bool.false_eq_true, ↓reduceIte,
          List.nil_append, List.mem_singleton, reduceCtorEq] at adopted
      | true =>
          have listed : .adopt producer ∈ items.map (fun item => HostEffect.adopt
              item.occurrence) := by
            simpa only [graphEffects, active, ↓reduceIte, List.mem_append,
              List.mem_singleton, reduceCtorEq, or_false]
              using adopted
          obtain ⟨item, selected, same⟩ := List.mem_map.mp listed
          have identity : item.occurrence = producer := HostEffect.adopt.inj same
          have absent := origins.freshProducer_streamAbsent generated (identity.symm ▸ known)
            (fresh.2.2.1 item.occurrence (List.mem_map_of_mem selected))
          have notice := ReferenceWorkQueue.State.streamItems_fresh_notice stream items active
            selected (matching.itemChildStreams_complete selected (identity.symm ▸ known))
            absent available
          have tasksKnown : ∀ item ∈ items, ∀ task ∈ item.work.tasks,
              ReferenceWorkQueue.TaskMatches work task := by
            intro item member task supplied
            obtain ⟨address, payload, shape, located⟩ :=
              matching.streamItem_childTask_producer member supplied
            exact ⟨⟨address, payload, some item.occurrence, shape, located⟩,
              matching.streamItem_childTask_groupsExact member supplied⟩
          have frames := streamItems_cacheFrames_of_structural generated canonical source.roots.live
            source.roots.retired source.tasks source.parent.children keys stream items matching
            available
          have drainFrames := streamItems_drainFrames generated canonical source.roots.live
            source.roots.retired source.tasks source.parent.children stream items matching available
          have projection := State.streamItems_cacheProjection (state := { queue }) keys stream
            items tasksKnown rfl available frames ⟨parents, drainFrames⟩
          apply Or.inl
          apply RecordTargetRepresented.activeStream
          simp only [State.handleGraphEvent, cached]
          have roots := congrArg (fun pair => pair.1.rootStreams) projection
          have rootsFrame (current : ReferenceWorkQueue.State)
              : (current.cacheTaskFailures available).rootStreams = current.rootStreams := by
            have sameRoots := congrArg ReferenceWorkQueue.State.rootStreams
              (current.cacheTaskFailures_frame available)
            exact sameRoots
          rw [rootsFrame, rootsFrame] at roots
          rw [roots]
          exact queue.streamItems_streamRoots_cover stream items available
            (List.mem_append_right _ notice)
  | taskFailure | groupFailure | streamSuccess => cases adopted
  | streamFailure stream errors =>
      simp only [graphEffects] at adopted
      split at adopted <;> simp at adopted

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
