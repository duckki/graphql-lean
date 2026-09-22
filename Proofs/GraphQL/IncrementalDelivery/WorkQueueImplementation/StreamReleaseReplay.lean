import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamReleaseAccounting

/-! One publication inventory supports stream release through every raw input batch. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (StreamItemValue WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Task and item handlers can release stored producers through recursive draining
-----------------------------------------------------------------------------------------

/-- Output without group-success events has no task-produced stream notice to justify.
Witness: a carrier at an index would belong to the output, contradicting its exclusion.
-/
theorem StreamReleasePublications.of_noGroupSuccess {work published events}
    (absent
      : ∀ group groups streams,
          Execution.WorkQueueEvent.groupSuccess group groups streams ∉ events)
    : StreamReleasePublications work published events := by
  intro index group groups streams atEvent
  exact False.elim (absent group groups streams (List.mem_of_getElem? atEvent))

/-- Failed tasks emit group failures only, never successful stream-release carriers.
Witness: the contributor fold either appends a failure or silently caches group errors.
-/
theorem State.taskFailure_noGroupSuccess (queue : State) (occurrence : Occurrence)
    (errors : Nat) (group : Execution.DeliveryNode) (groups streams)
    : Execution.WorkQueueEvent.groupSuccess group groups streams
      ∉ (queue.taskFailure occurrence errors).2 := by
  let step (acc : State × List WorkQueueEvent) (owner : Execution.DeliveryNode) :=
    match acc.1.groupNode? owner.key with
    | none => acc
    | some node =>
        if acc.1.rootGroups.contains owner.key then
          let (next, failure) := acc.1.finishGroupFailure node errors
          (next, acc.2 ++ [failure])
        else (acc.1.putGroupNode
          { node with pending := node.pending - 1
                      failure := some (node.failure.getD 0 + errors) }, acc.2)
  have loop (owners : List Execution.DeliveryNode) (acc : State × List WorkQueueEvent)
      (prior : Execution.WorkQueueEvent.groupSuccess group groups streams ∉ acc.2)
      : Execution.WorkQueueEvent.groupSuccess group groups streams ∉ (owners.foldl step acc).2 := by
    induction owners generalizing acc with
    | nil => exact prior
    | cons owner rest ih =>
        apply ih
        unfold step
        split
        · exact prior
        · split
          · simpa [State.finishGroupFailure] using prior
          · exact prior
  unfold State.taskFailure
  split
  · simp
  · split
    · simp
    exact loop _ (_, []) (by simp)

/-- An item handler's final drain releases task-produced streams with prior producer values.
Witness: parentless item integration preserves the joint state invariant, then draining
supplies one common fresh inventory. The leading item event adds no object-publication offset.
-/
theorem State.PublicationInventory.streamItems_streamRelease {queue : State}
    {work property published} (inventory : queue.PublicationInventory property published)
    (settled : queue.ChildStreamsSettled) (links : queue.ChildStreamsMatchWork work)
    (generated : ExecutedWork work) (stream : Execution.DeliveryNode)
    (items : List StreamItem)
    : ∃ added : List ObjectPublication,
        added.map Prod.snd
          = (queue.streamItems stream items).2.flatMap WorkQueueEvent.objectValues
        ∧ (queue.streamItems stream items).1.PublicationInventory property
            (published ++ added)
        ∧ StreamReleasePublications work added (queue.streamItems stream items).2 := by
  let step (acc : State × List Execution.DeliveryNode
      × List Execution.DeliveryNode × List StreamItemValue) (item : StreamItem) :=
    let (current, groups, streams, values) := acc
    let (integrated, newWork) := current.maybeIntegrateWork item.work
    let (pruned, nonempty) := integrated.pruneEmptyGroups newWork.newGroups
    (pruned.startNewWork { newWork with newGroups := nonempty },
      groups ++ nonempty, streams ++ newWork.newStreams, values ++ [item.value])
  have loop (more : List StreamItem)
      (acc : State × List Execution.DeliveryNode
        × List Execution.DeliveryNode × List StreamItemValue)
      (prior : acc.1.PublicationInventory property published)
      (ready : acc.1.ChildStreamsSettled) (childLinks : acc.1.ChildStreamsMatchWork work)
      : (more.foldl step acc).1.PublicationInventory property published
        ∧ (more.foldl step acc).1.ChildStreamsSettled
        ∧ (more.foldl step acc).1.ChildStreamsMatchWork work := by
    induction more generalizing acc with
    | nil => exact ⟨prior, ready, childLinks⟩
    | cons item rest ih =>
        exact ih _ ⟨prior.unique, prior.provenance,
          ((prior.stored.maybeIntegrateWork item.work).pruneEmptyGroups _).startNewWork _⟩
          (((ready.integrateRoots item.work).pruneEmptyGroups _).startNewWork _)
          (((childLinks.integrateRoots item.work).pruneEmptyGroups _).startNewWork _)
  obtain ⟨ledger, ready, childLinks⟩ := loop items (queue, [], [], []) inventory settled links
  unfold State.streamItems
  split
  · exact ⟨[], rfl, by simpa using inventory, StreamReleasePublications.nil work⟩
  · obtain ⟨added, values, final, supported⟩ :=
      ledger.drainReadyGroups_streamRelease ready childLinks generated
    refine ⟨added, ?_, final, ?_⟩
    · simpa only [List.flatMap_cons, WorkQueueEvent.objectValues, List.nil_append] using values
    · have control : StreamReleasePublications work []
          [.streamValues stream (items.foldl step (queue, [], [], [])).2.2.2
            (items.foldl step (queue, [], [], [])).2.1
            (items.foldl step (queue, [], [], [])).2.2.1] :=
        .of_noGroupSuccess (by intros; simp)
      exact control.append supported rfl

/-- Every handler extends one ledger with exact values and strict-prefix release support.
Witness: task and item handlers thread a common inventory through recursive drains; failure
and stream-close controls emit no group-success carriers.
-/
theorem State.PublicationInventory.handleGraphEvent_streamRelease {queue : State}
    {work property published} (inventory : queue.PublicationInventory property published)
    (settled : queue.ChildStreamsSettled) (links : queue.ChildStreamsMatchWork work)
    (generated : ExecutedWork work) (event : GraphEvent)
    (source : event.MatchesWork work)
    (allowed
      : ∀ occurrence result,
          event = .taskSuccess occurrence result
          → property occurrence result.value ∧ occurrence ∉ published.map Prod.fst)
    : ∃ added : List ObjectPublication,
        added.map Prod.snd
          = (queue.handleGraphEvent event).2.flatMap WorkQueueEvent.objectValues
        ∧ (queue.handleGraphEvent event).1.PublicationInventory property
            (published ++ added)
        ∧ StreamReleasePublications work added (queue.handleGraphEvent event).2 := by
  cases event with
  | taskSuccess occurrence result =>
      exact inventory.taskSuccess_streamRelease settled links generated source
        (allowed _ _ rfl).1 (allowed _ _ rfl).2
  | taskFailure occurrence errors =>
      obtain ⟨added, values, final⟩ := inventory.handleGraphEvent
        (.taskFailure occurrence errors) allowed
      exact ⟨added, values, final, .of_noGroupSuccess
        (queue.taskFailure_noGroupSuccess occurrence errors)⟩
  | streamItems stream items =>
      exact inventory.streamItems_streamRelease settled links generated stream items
  | streamSuccess stream =>
      obtain ⟨added, values, final⟩ := inventory.handleGraphEvent (.streamSuccess stream) allowed
      refine ⟨added, values, final, .of_noGroupSuccess ?_⟩
      intro group groups streams
      simp only [State.handleGraphEvent, State.streamSuccess]
      split <;> simp
  | streamFailure stream errors =>
      obtain ⟨added, values, final⟩ := inventory.handleGraphEvent
        (.streamFailure stream errors) allowed
      refine ⟨added, values, final, .of_noGroupSuccess ?_⟩
      intro group groups streams
      simp only [State.handleGraphEvent, State.streamFailure]
      split <;> simp

-----------------------------------------------------------------------------------------
-- Concatenate eventwise release witnesses without choosing a different source matching
-----------------------------------------------------------------------------------------

/-- Raw replay retains exact publication labels and release support across all handlers.
Witness: source freshness licenses each new value; exact payload counts shift the next
handler's carrier offsets. Child-link invariants are preserved by the actual transitions.
-/
theorem State.PublicationInventory.rawEventReplay_streamRelease {queue : State}
    {work before published}
    (inventory : queue.PublicationInventory (ObjectValueFrom before) published)
    (settled : queue.ChildStreamsSettled) (links : queue.ChildStreamsMatchWork work)
    (generated : ExecutedWork work) (events : List GraphEvent)
    (valid : ValidGraphEvents work (before ++ events))
    : ∃ added : List ObjectPublication,
        added.map Prod.snd
          = (queue.rawEventReplay events).2.flatMap WorkQueueEvent.objectValues
        ∧ (queue.rawEventReplay events).1.PublicationInventory
            (ObjectValueFrom (before ++ events)) (published ++ added)
        ∧ StreamReleasePublications work added (queue.rawEventReplay events).2 := by
  induction events generalizing queue before published with
  | nil =>
      refine ⟨[], rfl, ?_, .nil work⟩
      simpa only [List.append_nil, State.rawEventReplay, List.foldl_nil] using inventory
  | cons event rest ih =>
      have earlier : (before ++ [event]).IsPrefix (before ++ event :: rest) :=
        ⟨rest, by simp⟩
      obtain ⟨matching, fresh, _⟩ := valid.atPrefix earlier
      have current := inventory.mono (fun _ _ source =>
        source.mono (List.subset_append_left before [event]))
      obtain ⟨first, values, after, firstSupport⟩ :=
        current.handleGraphEvent_streamRelease settled links generated event matching (by
          intro occurrence result same
          subst event
          exact ⟨⟨result, List.mem_append_right _ List.mem_cons_self, rfl⟩,
            inventory.fresh_success fresh⟩)
      obtain ⟨later, laterValues, final, laterSupport⟩ :=
        ih after (settled.handleGraphEvent event) (links.handleGraphEvent matching)
          (by simpa only [List.append_assoc, List.singleton_append] using valid)
      rw [State.rawEventReplay_cons]
      refine ⟨first ++ later, ?_, ?_, firstSupport.append laterSupport values⟩
      · simp only [List.map_append, List.flatMap_append, values, laterValues]
      · simpa only [List.append_assoc, List.singleton_append] using final

/-- The real batch wrapper preserves the same joint publication and release witness.
Witness: replay supplies it before termination; a terminal flag adds only a control event,
and a previously terminated queue emits nothing. No start or output-admission premise is used.
-/
theorem State.PublicationInventory.handleGraphEvents_streamRelease {queue : State}
    {work before published}
    (inventory : queue.PublicationInventory (ObjectValueFrom before) published)
    (settled : queue.ChildStreamsSettled) (links : queue.ChildStreamsMatchWork work)
    (generated : ExecutedWork work) (events : List GraphEvent)
    (valid : ValidGraphEvents work (before ++ events))
    : ∃ added : List ObjectPublication,
        added.map Prod.snd
          = (queue.handleGraphEvents events).2.flatMap WorkQueueEvent.objectValues
        ∧ (queue.handleGraphEvents events).1.PublicationInventory
            (ObjectValueFrom (before ++ events)) (published ++ added)
        ∧ StreamReleasePublications work added (queue.handleGraphEvents events).2 := by
  rw [State.handleGraphEvents_eq_rawEventReplay]
  split
  · refine ⟨[], rfl, ?_, .nil work⟩
    simpa only [List.append_nil] using inventory.mono
      (fun _ _ source => source.mono (List.subset_append_left before events))
  · obtain ⟨added, values, final, supported⟩ :=
      inventory.rawEventReplay_streamRelease settled links generated events valid
    dsimp only
    split
    · have control : StreamReleasePublications work [] [.workQueueTermination] :=
        .of_noGroupSuccess (by simp)
      refine ⟨added, ?_, ⟨final.unique, final.provenance, final.stored⟩, ?_⟩
      · simpa only [List.flatMap_append, List.flatMap_singleton,
          WorkQueueEvent.objectValues, List.append_nil] using values
      · simpa only [List.append_nil] using supported.append control values
    · exact ⟨added, values, final, supported⟩

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
