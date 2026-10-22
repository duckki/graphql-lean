import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.PublicationTransfer

/-! Actual publication keys justify the cleanup view's transfer exclusion. NodeRefs suffice:
no equality between a contributing descriptor and the carrier descriptor is assumed.+-/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
open GraphQL.IncrementalDelivery.WorkQueueSemantics (Occurrence)
open GraphQL.IncrementalDelivery.ReferenceWorkQueue (TaskNode GroupNode)
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)

private abbrev Kernel := ReferenceWorkQueue.State

-----------------------------------------------------------------------------------------
-- Every successful carrier comes from a group live in the prepared snapshot
-----------------------------------------------------------------------------------------

/-- Exact inversion of this handler's successful-key projection. -/
theorem mem_publicationRoots {key : Nat} {events : List WorkQueueEvent}
    : key ∈ publicationRoots events
      ↔ ∃ group groups streams,
          .groupSuccess group groups streams ∈ events ∧ group.ref = key := by
  constructor
  · intro member
    obtain ⟨event, emitted, selected⟩ := List.mem_filterMap.mp member
    cases event
    all_goals try contradiction
    case groupSuccess group groups streams =>
      exact ⟨group, groups, streams, emitted, Option.some.inj selected⟩
  · rintro ⟨group, groups, streams, emitted, same⟩
    exact List.mem_filterMap.mpr ⟨.groupSuccess group groups streams, emitted,
      congrArg some same⟩

private theorem edges_keys {before after : Kernel} (edges : after.GroupEdgesFrom before)
    : after.GroupRefsIncluded before := by
  intro key member
  obtain ⟨node, present, same⟩ := List.mem_map.mp member
  cases found : after.groupNode? key with
  | none =>
      have absent := List.find?_eq_none.mp found node present
      simp [same] at absent
  | some selected =>
      obtain ⟨old, earlier, _⟩ := edges key selected found
      exact List.mem_map.mpr ⟨old, List.mem_of_find?_eq_some earlier,
        ReferenceWorkQueue.State.groupNode?_ref earlier⟩

private theorem flush_publicationRoots (queue : Kernel) (node : GroupNode)
    {key : Nat} (published : key ∈ publicationRoots (queue.finishGroupSuccess node).2.1)
    : key = node.group.node.ref := by
  obtain ⟨group, groups, streams, carrier, same⟩ := mem_publicationRoots.mp published
  obtain ⟨index, selected⟩ := List.mem_iff_getElem?.mp carrier
  obtain ⟨_, descriptor, _, _⟩ := queue.finishGroupSuccess_index_prefix node selected
  exact same.symm.trans (congrArg Execution.DeliveryNode.ref descriptor.symm)

/-- Every successful carrier in a bounded mixed drain was live before that drain.
No sufficient-budget, forest, source, or generated-work premise is needed.
-/
theorem drainReadyGroups_go_publicationRoots_live (fuel : Nat) (queue : Kernel)
    : (publicationRoots
        (ReferenceWorkQueue.State.drainReadyGroups.go fuel queue).2).Subset
        (queue.groupNodes.map (fun node => node.group.node.ref)) := by
  induction fuel generalizing queue with
  | zero => intro key member; cases member
  | succ fuel ih =>
      unfold ReferenceWorkQueue.State.drainReadyGroups.go
      dsimp only
      split
      · intro key member; cases member
      · rename_i node selected
        have live : node ∈ queue.groupNodes := by
          obtain ⟨key, _, choice⟩ := List.exists_of_findSome?_eq_some selected
          cases found : queue.groupNode? key with
          | none => simp [found] at choice
          | some candidate =>
              simp only [found] at choice
              change (if _ then some candidate else none) = some node at choice
              split at choice
              · cases Option.some.inj choice
                exact List.mem_of_find?_eq_some found
              · contradiction
        cases cached : queue.rejectedTask? node with
        | none =>
            dsimp only
            intro key published
            rw [publicationRoots, List.filterMap_append] at published
            rcases List.mem_append.mp published with first | later
            · have same := flush_publicationRoots queue node first
              exact same.symm ▸ List.mem_map.mpr ⟨node, live, rfl⟩
            · have present := ih _ later
              rw [(ReferenceWorkQueue.State.startNewWork_groupCore _ _).1] at present
              exact edges_keys (queue.finishGroupSuccess_descendants node).1 key present
        | some rejected =>
            dsimp only
            intro key published
            rw [publicationRoots, List.filterMap_append] at published
            rcases List.mem_append.mp published with first | later
            · obtain ⟨group, groups, streams, carrier, _⟩ := mem_publicationRoots.mp first
              exact False.elim (queue.taskFailure_noGroupSuccess _ _ group groups streams carrier)
            · exact ((queue.taskFailure_groupNodes_sublist _ _).map
                (fun node => node.group.node.ref)).subset (ih _ later)

private theorem fold_publicationRoots_live (queue : Kernel)
    (groups : List Execution.DeliveryNode)
    : let folded := groups.foldl ReferenceWorkQueue.successGroupStep (queue, [], {})
      folded.1.GroupRefsIncluded queue
      ∧ (publicationRoots folded.2.1).Subset
          (queue.groupNodes.map (fun node => node.group.node.ref)) := by
  have loop (more : List Execution.DeliveryNode)
      (current : Kernel) (events : List WorkQueueEvent) (released : ReferenceWorkQueue.NewWork)
      (keys : current.GroupRefsIncluded queue)
      (known : (publicationRoots events).Subset (queue.groupNodes.map (fun node => node.group.node.ref)))
      : let folded := more.foldl ReferenceWorkQueue.successGroupStep (current, events, released)
        folded.1.GroupRefsIncluded queue
        ∧ (publicationRoots folded.2.1).Subset
            (queue.groupNodes.map (fun node => node.group.node.ref)) := by
    induction more generalizing current events released with
    | nil => exact ⟨keys, known⟩
    | cons group rest ih =>
        simp only [List.foldl_cons, ReferenceWorkQueue.successGroupStep]
        split
        · exact ih _ _ _ keys known
        · rename_i node found
          let updated := current.putGroupNode { node with pending := node.pending - 1 }
          have updatedKeys : updated.GroupRefsIncluded queue := by
            intro key member
            rw [ReferenceWorkQueue.State.putGroupNode_refs] at member
            exact keys key member
          split
          · have nextKeys := (edges_keys (updated.finishGroupSuccess_descendants
                { node with pending := node.pending - 1 }).1).trans updatedKeys
            apply ih _ _ _ nextKeys
            intro key published
            rw [publicationRoots, List.filterMap_append] at published
            rcases List.mem_append.mp published with earlier | now
            · exact known earlier
            · have same := flush_publicationRoots updated
                { node with pending := node.pending - 1 } now
              rw [same]
              exact keys _ (List.mem_map.mpr ⟨node, List.mem_of_find?_eq_some found, rfl⟩)
          · exact ih _ _ _ updatedKeys known
  exact loop groups queue [] {} (fun _ member => member)
    (by intro key member; cases member)

/-- Successful-key exclusion cannot refer to a contributor absent from preparation.
The exact success fold and mixed drain only close existing records. No generated-work,
health, forest, descriptor-equality, or source premise is needed for this lookup fact.
-/
theorem eagerRegistrationSnapshot_publicationRoots_live (queue : Kernel)
    (event : GraphEvent)
    : (publicationRoots (queue.handleGraphEvent event).2).Subset
        ((eagerRegistrationSnapshot queue event).groupNodes.map
          (fun node => node.group.node.ref)) := by
  cases event with
  | taskSuccess occurrence result =>
      cases found : queue.taskNode? occurrence with
      | none =>
          simp only [ReferenceWorkQueue.State.handleGraphEvent,
            ReferenceWorkQueue.State.taskSuccess, found, publicationRoots, List.filterMap_nil]
          intro key member; cases member
      | some node =>
          let snapshot := eagerRegistrationSnapshot queue (.taskSuccess occurrence result)
          have prepared := fold_publicationRoots_live snapshot node.task.groups
          have snapshotEq : snapshot =
              ((queue.putTaskNode { node with value := some result.value }).maybeIntegrateWork
                result.work (some occurrence)).1 := by
            simp only [snapshot, eagerRegistrationSnapshot, found]
          rw [snapshotEq] at prepared
          change (publicationRoots (queue.handleGraphEvent _).2).Subset
            (snapshot.groupNodes.map (fun node => node.group.node.ref))
          rw [snapshotEq]
          simp only [ReferenceWorkQueue.State.handleGraphEvent]
          rw [queue.taskSuccess_eq occurrence result node found]
          change (publicationRoots (_ ++ _)).Subset _
          intro key published
          rw [publicationRoots, List.filterMap_append] at published
          rcases List.mem_append.mp published with first | later
          · exact prepared.2 first
          · apply prepared.1 key
            have present := drainReadyGroups_go_publicationRoots_live _ _ later
            rwa [(ReferenceWorkQueue.State.startNewWork_groupCore _ _).1] at present
  | streamItems stream items =>
      cases active : queue.rootStreams.contains stream.ref with
      | false =>
          simp only [ReferenceWorkQueue.State.handleGraphEvent,
            ReferenceWorkQueue.State.streamItems, active, Bool.not_false, ↓reduceIte,
            publicationRoots, List.filterMap_nil]
          intro key member; cases member
      | true =>
          rw [eagerRegistrationSnapshot_streamItems queue stream items active]
          change (publicationRoots (queue.streamItems stream items).2).Subset _
          rw [queue.streamItems_eq stream items]
          simp only [active, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          intro key published
          exact drainReadyGroups_go_publicationRoots_live _ _ published
  | taskFailure occurrence errors =>
      intro key published
      obtain ⟨group, groups, streams, carrier, _⟩ := mem_publicationRoots.mp published
      exact False.elim (queue.taskFailure_noGroupSuccess occurrence errors _ _ _ carrier)
  | streamSuccess stream =>
      simp only [ReferenceWorkQueue.State.handleGraphEvent, ReferenceWorkQueue.State.streamSuccess]
      split <;> intro key member <;> cases member
  | streamFailure stream errors =>
      simp only [ReferenceWorkQueue.State.handleGraphEvent, ReferenceWorkQueue.State.streamFailure]
      split <;> intro key member <;> cases member

-----------------------------------------------------------------------------------------
-- The exact key-based exclusion transfers its held source through the complete handler
-----------------------------------------------------------------------------------------

/-- The actual delayed snapshot has the same contributor keys as the eager proof view. -/
theorem registrationSnapshot_publicationRoots_live (queue : Kernel) (event : GraphEvent)
    (projection : SnapshotProjection queue event)
    : (publicationRoots (queue.handleGraphEvent event).2).Subset
        ((registrationSnapshot queue event).groupNodes.map
          (fun node => node.group.node.ref)) := by
  have keys := congrArg (fun queue : Kernel => queue.groupNodes.map
    (fun node => node.group.node.ref)) projection.core
  change (registrationSnapshot queue event).groupNodes.map (fun node => node.group.node.ref)
    = (eagerRegistrationSnapshot queue event).groupNodes.map (fun node => node.group.node.ref) at keys
  rw [keys]
  exact eagerRegistrationSnapshot_publicationRoots_live queue event

/-- A contributing key published by this dispatch transfers every attached buffered source.
Carrier provenance derives initial liveness; generated retirement derives uncancelledness.
Only key equality is needed, exactly as in the public effect filter.
-/
theorem generatedSnapshot_publishedKeyTransfer {work inputs event occurrence}
    {node : TaskNode} {value key owner groups streams}
    (generated : ReferenceWorkQueue.ExecutedWork work)
    (valid : ReferenceWorkQueue.ValidGraphEvents work (inputs.flatten ++ [event]))
    (started : ReferenceWorkQueue.inputsStarted work (inputs ++ [[event]]) = true)
    (found
      : (registrationSnapshot ((State.initialize work).runNormalized inputs).1.queue
          event).taskNode?
          occurrence
        = some node)
    (stored : node.value = some value) (held : key ∈ node.childStreams)
    (contributes : owner.ref ∈ node.task.groups.map Execution.DeliveryNode.ref)
    (carrier
      : WorkQueueEvent.groupSuccess owner groups streams
        ∈ ((((State.initialize work).runNormalized inputs).1.queue).handleGraphEvent
            event).2)
    : key
        ∈ ((((State.initialize work).runNormalized inputs).1.queue).handleGraphEvent
            event).2.flatMap
            ReferenceWorkQueue.rawStreamNoticeRefs
      ∧ key
        ∈ (({ state := ((State.initialize work).runNormalized inputs).1 }
            : GraphBatchResult).handleGraphEvent
            event).state.queue.rootStreams
      ∧ .stream key
        ∈ (({ state := ((State.initialize work).runNormalized inputs).1 }
            : GraphBatchResult).handleGraphEvent
            event).state.cleanupTargets := by
  let before := ((State.initialize work).runNormalized inputs).1
  have published : owner.ref ∈ publicationRoots (before.queue.handleGraphEvent event).2 :=
    mem_publicationRoots.mpr ⟨owner, groups, streams, carrier, rfl⟩
  obtain ⟨beforeRaw, earlierStarted, accepted⟩ := generatedReplay_beforeNext generated valid started
  have projection := generatedSnapshot_projection generated valid earlierStarted
  have live := registrationSnapshot_publicationRoots_live before.queue event projection published
  have conservation := generatedSnapshot_bufferedStreamsConserved generated valid started
  dsimp only at conservation
  have rawCarrier := carrier
  rw [beforeRaw] at rawCarrier
  obtain ⟨_, _, retired, _, uncancelled⟩ :=
    generated.replayGraphEvents_successfulCarrier_retiredHealthy valid accepted rawCarrier
  rw [ReferenceWorkQueue.State.replayGraphEvents_append, ← beforeRaw] at retired uncancelled
  have notice := conservation.retired_notice found stored held contributes live retired.2 uncancelled
  have dispatch := generatedReplay_dispatchProjection generated valid started
  exact ⟨notice, (congrArg (fun pair => pair.1.rootStreams) dispatch).symm ▸
      graphEvent_newStream_active _ _ notice,
    GraphBatchResult.releasedStream_cleanupTarget _ _ dispatch notice⟩

/-- Generated construction target for the public transfer exclusion. A success/item
handler's nonpending prepared buffer has really transferred, not merely disappeared.
No initial live-owner, exact carrier descriptor, internal ledger, or native inventory
premise is supplied by the caller.
-/
def GeneratedPublicationExclusionTransfer : Prop :=
  ∀ work inputs event,
    ReferenceWorkQueue.ExecutedWork work
    → ReferenceWorkQueue.ValidGraphEvents work (inputs.flatten ++ [event])
    → ReferenceWorkQueue.inputsStarted work (inputs ++ [[event]]) = true
    → (match event with
        | .taskSuccess _ _ | .streamItems _ _ => True
        | _ => False)
    → ∀ (occurrence : Occurrence) (node : TaskNode) key,
        let before := ((State.initialize work).runNormalized inputs).1
        let snapshot := registrationSnapshot before.queue event
        let reduced := ({ state := before } : GraphBatchResult).handleGraphEvent event
        snapshot.taskNode? occurrence = some node
        → node.value.isSome = true
        → key ∈ node.childStreams
        → pruningPending snapshot event (before.queue.handleGraphEvent event).2 occurrence
          = false
        → key
            ∈ (before.queue.handleGraphEvent event).2.flatMap
                ReferenceWorkQueue.rawStreamNoticeRefs
          ∧ key ∈ reduced.state.queue.rootStreams
          ∧ .stream key ∈ reduced.state.cleanupTargets

/-- Exact catalogue contributors and the actual false filter extract a successful key.
The same full-handler conservation/retirement witness constructs notice, root, and stop reachability.
-/
theorem GeneratedPublicationExclusionTransfer_holds
    : GeneratedPublicationExclusionTransfer := by
  intro work inputs event generated valid started release occurrence node key
  dsimp only
  intro found stored held excluded
  obtain ⟨_, earlierStarted, _⟩ := generatedReplay_beforeNext generated valid started
  obtain ⟨task, catalogue, sameGroups⟩ := generatedSnapshot_taskCatalogue generated valid
    earlierStarted found
  have published : task.groups.any
      (fun owner => (publicationRoots
        ((((State.initialize work).runNormalized inputs).1.queue).handleGraphEvent event).2).contains
        owner.ref) = true := by
    cases event with
    | taskSuccess | streamItems =>
        simpa only [pruningPending, catalogue, Bool.not_false, Bool.true_and,
          Bool.not_eq_false'] using excluded
    | taskFailure | streamSuccess | streamFailure => cases release
  obtain ⟨contributor, member, selected⟩ := List.any_eq_true.mp published
  obtain ⟨owner, groups, streams, carrier, sameKey⟩ :=
    mem_publicationRoots.mp (List.contains_iff_mem.mp selected)
  cases valueEq : node.value with
  | none => simp [valueEq] at stored
  | some value =>
      apply generatedSnapshot_publishedKeyTransfer generated valid started found valueEq held
        (owner := owner) (groups := groups) (streams := streams) _ carrier
      rw [sameKey, ← sameGroups]
      exact List.mem_map.mpr ⟨contributor, member, rfl⟩

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
