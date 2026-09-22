import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.MembershipExclusionHandlers

/-! Source replay derives publication exclusion from existing source freshness and order. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Event-by-event replay retains exact publications and their global membership removal
-----------------------------------------------------------------------------------------

/-- Legal source replay cannot reintroduce any membership already published by this ledger.
Witness: every fresh input's children are unsettled in the earlier source prefix. Exact
publication provenance therefore excludes them from the prior ledger, and each handler
retains that exclusion while adding its actual selected publications.
-/
theorem State.PublicationInventory.rawEventReplay_memberships
    {queue : State} {work before published}
    (inventory : queue.PublicationInventory (ObjectValueFrom before) published)
    (absent : ∀ publication ∈ published, queue.TaskMembershipAbsent publication.1)
    (events : List GraphEvent) (valid : ValidGraphEvents work (before ++ events))
    : ∃ added : List ObjectPublication,
        added.map Prod.snd
          = (queue.rawEventReplay events).2.flatMap WorkQueueEvent.objectValues
        ∧ (queue.rawEventReplay events).1.PublicationInventory
            (ObjectValueFrom (before ++ events)) (published ++ added)
        ∧ ∀ publication ∈ published ++ added,
            (queue.rawEventReplay events).1.TaskMembershipAbsent publication.1 := by
  induction events generalizing queue before published with
  | nil =>
      refine ⟨[], rfl, ?_, ?_⟩
      · simpa only [List.append_nil, State.rawEventReplay, List.foldl_nil] using inventory
      · simpa only [List.append_nil, State.rawEventReplay, List.foldl_nil] using absent
  | cons event rest ih =>
      have earlier : (before ++ [event]).IsPrefix (before ++ event :: rest) :=
        ⟨rest, by simp⟩
      have eventLaws := valid.atPrefix earlier
      have priorValid := valid.prefix (List.prefix_append before (event :: rest))
      have current := inventory.mono (fun _ _ source =>
        source.mono (List.subset_append_left before [event]))
      obtain ⟨first, values, after, removed⟩ := current.handleGraphEvent_memberships absent event
        (by
          intro occurrence result same
          subst event
          exact ⟨⟨result, List.mem_append_right _ List.mem_cons_self, rfl⟩,
            inventory.fresh_success eventLaws.2.1⟩)
        (fun _ member => eventLaws.1.childTask_not_published priorValid eventLaws.2.1
          inventory member)
      obtain ⟨later, laterValues, final, excluded⟩ := ih after removed (by
        simpa only [List.append_assoc, List.singleton_append] using valid)
      refine ⟨first ++ later, ?_, ?_, ?_⟩
      · rw [State.rawEventReplay_cons, List.map_append]
        simp only [List.flatMap_append, ← values, ← laterValues]
      · rw [State.rawEventReplay_cons]
        simpa only [List.append_assoc, List.singleton_append] using final
      · rw [State.rawEventReplay_cons]
        simpa only [List.append_assoc] using excluded

/-- Created-queue replay retains an exact publication inventory with no live memberships
for any delivered object occurrence. Witness: initialization has no publications or stored
values; the source-valid replay theorem derives all integration exclusions itself. This
requires neither output admission nor generated-work or host-start assumptions.
-/
theorem createWorkQueue_rawEventReplay_publicationMemberships {work : Execution.Work}
    {events : List GraphEvent} (valid : ValidGraphEvents work events)
    : ∃ published : List ObjectPublication,
        published.map Prod.snd
          = ((State.initialize (Work.fromExecution work)).rawEventReplay events).2.flatMap
              WorkQueueEvent.objectValues
        ∧ ((State.initialize (Work.fromExecution work)).rawEventReplay
            events).1.PublicationInventory
            (ObjectValueFrom events) published
        ∧ ∀ publication ∈ published,
            ((State.initialize (Work.fromExecution work)).rawEventReplay
              events).1.TaskMembershipAbsent
              publication.1 := by
  have initial : (State.initialize (Work.fromExecution work)).PublicationInventory
      (ObjectValueFrom []) [] :=
    ⟨by simp, by simp, createWorkQueue_storedValues _ _⟩
  simpa only [List.nil_append]
    using initial.rawEventReplay_memberships (by simp) events valid

-----------------------------------------------------------------------------------------
-- Public batch processing has the same exclusion, including termination-only output
-----------------------------------------------------------------------------------------

/-- Batch processing preserves membership exclusion alongside exact object publications.
Witness: the event fold derives freshness from source validity. The outer wrapper either
leaves the queue untouched or appends only a termination control and updates its flag.
-/
theorem State.PublicationInventory.handleGraphEvents_memberships {queue : State}
    {work before published}
    (inventory : queue.PublicationInventory (ObjectValueFrom before) published)
    (absent : ∀ publication ∈ published, queue.TaskMembershipAbsent publication.1)
    (events : List GraphEvent) (valid : ValidGraphEvents work (before ++ events))
    : ∃ added : List ObjectPublication,
        added.map Prod.snd
          = (queue.handleGraphEvents events).2.flatMap WorkQueueEvent.objectValues
        ∧ (queue.handleGraphEvents events).1.PublicationInventory
            (ObjectValueFrom (before ++ events)) (published ++ added)
        ∧ ∀ publication ∈ published ++ added,
            (queue.handleGraphEvents events).1.TaskMembershipAbsent publication.1 := by
  rw [State.handleGraphEvents_eq_rawEventReplay]
  split
  · refine ⟨[], rfl, ?_, ?_⟩
    · simpa only [List.append_nil] using inventory.mono
        (fun _ _ source => source.mono (List.subset_append_left before events))
    · simpa only [List.append_nil] using absent
  · obtain ⟨added, values, final, removed⟩ :=
      inventory.rawEventReplay_memberships absent events valid
    dsimp only
    split
    · refine ⟨added, ?_, ⟨final.unique, final.provenance, final.stored⟩, removed⟩
      simpa only [List.flatMap_append, List.flatMap_singleton, WorkQueueEvent.objectValues,
        List.append_nil] using values
    · exact ⟨added, values, final, removed⟩

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
