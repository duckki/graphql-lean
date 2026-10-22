import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.PublicationContributors
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.BatchOutputReplay

/-! Publication adjacency, ownership and successful-source provenance retain actual batching. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Actual raw batches retain each value block's immediate successful carrier. -/
theorem State.rawBatches_publicationPairs (queue : State)
    (batches : List (List GraphEvent))
    : GroupPublicationPairs (queue.rawBatches batches).2 := by
  induction batches generalizing queue with
  | nil => exact .nil
  | cons batch rest ih =>
      exact (queue.handleGraphEvents_publicationPairs batch).append (ih _)

/-- Contributor metadata follows every FIFO input under one fixed rejection snapshot. -/
theorem State.ContributorProvenance.replayGraphEvents {queue work}
    (provenance : State.ContributorProvenance queue work)
    (events : List GraphEvent) (matching : ∀ event ∈ events, event.MatchesWork work)
    (available : List (Occurrence × Nat))
    : (queue.replayGraphEvents events available).ContributorProvenance work := by
  induction events generalizing queue with
  | nil => exact provenance
  | cons event rest ih =>
      exact ih (provenance.dispatchGraphEvent event (matching event List.mem_cons_self) available)
        (fun next member => matching next (List.mem_cons_of_mem _ member))

/-- Batch-end forwarding changes neither contributor metadata nor object ownership. -/
theorem State.ContributorProvenance.handleGraphEvents {queue work}
    (provenance : State.ContributorProvenance queue work)
    (events : List GraphEvent) (matching : ∀ event ∈ events, event.MatchesWork work)
    : (queue.handleGraphEvents events).1.ContributorProvenance work
      ∧ RawPublicationContributors (queue.handleGraphEvents events).2 := by
  have state := provenance.replayGraphEvents events matching (GraphEvent.availableFailures events)
  rw [← State.rawEventReplay_state _ _ (GraphEvent.availableFailures events)] at state
  have output := provenance.rawEventReplay_outputs events matching
    (GraphEvent.availableFailures events)
  rw [State.handleGraphEvents_eq_rawEventReplay queue events]
  split
  · exact ⟨provenance, by intro group values emitted; cases emitted⟩
  · dsimp only
    split
    · refine ⟨⟨state.registered, state.memberships, state.stored⟩,
        output.append ?_⟩
      intro group values emitted
      simp at emitted
    · exact ⟨state, output⟩

/-- Contributor metadata and releasing-owner membership hold throughout actual host batches. -/
theorem State.ContributorProvenance.rawBatches {queue work}
    (provenance : State.ContributorProvenance queue work)
    (batches : List (List GraphEvent))
    (matching : ∀ event ∈ batches.flatten, event.MatchesWork work)
    : (queue.rawBatches batches).1.ContributorProvenance work
      ∧ RawPublicationContributors (queue.rawBatches batches).2 := by
  induction batches generalizing queue with
  | nil => exact ⟨provenance, by intro group values emitted; cases emitted⟩
  | cons batch rest ih =>
      have first := provenance.handleGraphEvents batch
        (fun event member => matching event (by simp [member]))
      have later := ih first.1 (fun event member => matching event (by simp [member]))
      exact ⟨later.1, first.2.append later.2⟩

/-- Actual batch output uses a contributing releasing group for every object payload. -/
theorem createWorkQueue_rawBatches_publicationContributors {work batches}
    (valid : ValidGraphEvents work (List.flatten batches))
    : RawPublicationContributors
        ((State.initialize (Work.fromExecution work)).rawBatches batches).2 := by
  have initial : (State.initialize (Work.fromExecution work)).ContributorProvenance work :=
    ⟨createWorkQueue_fromSpec_registeredTasksMatch work,
      createWorkQueue_groupMembershipSound _, createWorkQueue_storedValues _ _⟩
  exact (initial.rawBatches batches (fun _ member => valid.event_matches member)).2

/-- One occurrence-labelled inventory follows all actual host batches and object output. -/
theorem State.PublicationInventory.rawBatches {queue work before published}
    (inventory : State.PublicationInventory queue (ObjectValueFrom before) published)
    (batches : List (List GraphEvent))
    (valid : ValidGraphEvents work (before ++ batches.flatten))
    : ∃ added : List ObjectPublication,
        added.map Prod.snd
          = (queue.rawBatches batches).2.flatMap WorkQueueEvent.objectValues
        ∧ (queue.rawBatches batches).1.PublicationInventory
            (ObjectValueFrom (before ++ batches.flatten)) (published ++ added) := by
  induction batches generalizing queue before published with
  | nil =>
      exact ⟨
        [],
        rfl,
        by
          simpa only [State.rawBatches, List.flatten_nil, List.append_nil] using inventory
      ⟩
  | cons batch rest ih =>
      obtain ⟨first, firstValues, next⟩ := inventory.handleGraphEvents batch
        (valid.prefix ⟨rest.flatten, by simp [List.append_assoc]⟩)
      obtain ⟨later, laterValues, final⟩ := ih next
        (by simpa only [List.flatten_cons, List.append_assoc] using valid)
      refine ⟨first ++ later, ?_, ?_⟩
      · simp only [List.map_append, State.rawBatches, List.flatMap_append, firstValues, laterValues]
      · simpa only [State.rawBatches, List.flatten_cons, List.append_assoc] using final

/-- Every actual batched object value retains its exact successful source event. -/
theorem createWorkQueue_rawBatches_valueSource {work batches group values value}
    (valid : ValidGraphEvents work (List.flatten batches))
    (emitted
      : .groupValues group values
        ∈ ((State.initialize (Work.fromExecution work)).rawBatches batches).2)
    (member : value ∈ values)
    : ∃ occurrence result,
        GraphEvent.taskSuccess occurrence result ∈ batches.flatten
        ∧ result.value = value
        ∧ (GraphEvent.taskSuccess occurrence result).MatchesWork work := by
  have initial : (State.initialize (Work.fromExecution work)).PublicationInventory
      (ObjectValueFrom []) [] :=
    ⟨by simp, by simp, createWorkQueue_storedValues _ _⟩
  obtain ⟨published, exactValues, inventory⟩ := initial.rawBatches batches valid
  have inValues : value ∈ published.map Prod.snd := by
    rw [exactValues]
    exact List.mem_flatMap.mpr ⟨_, emitted, member⟩
  obtain ⟨publication, selected, same⟩ := List.mem_map.mp inValues
  obtain ⟨result, supplied, stored⟩ := inventory.provenance publication
    (List.mem_append_right _ selected)
  exact ⟨publication.1, result, supplied, stored.trans same, valid.event_matches supplied⟩

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
