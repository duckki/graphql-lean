import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ReplayPublicationLedger

/-! Stored-value conservation composes on the already chosen source-replay ledger. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Permanent registration rules out a vanished contributor reappearing later
-----------------------------------------------------------------------------------------

/-- An earlier registered key that is live after replay was already live before replay.
Witness: otherwise it was retired, and every source handler preserves that retirement.
No source matching, freshness, or admission premise is needed for this backward fact.
-/
theorem State.replayGraphEvents_live_registered {queue : State} {key}
    (registered : key ∈ queue.registeredGroups) (events : List GraphEvent)
    {owner} (live : (queue.replayGraphEvents events).groupNode? key = some owner)
    : ∃ earlier, queue.groupNode? key = some earlier := by
  cases found : queue.groupNode? key with
  | some node => exact ⟨node, rfl⟩
  | none =>
      have retired := State.RetiredGroup.of_lookup_none registered found
      have preserve (events : List GraphEvent) (current : State)
          (prior : current.RetiredGroup key)
          : (current.replayGraphEvents events).RetiredGroup key := by
        induction events generalizing current with
        | nil => exact prior
        | cons event rest ih => exact ih _ (prior.handleGraphEvent event)
      have absent := (preserve events queue retired).lookup_none
      rw [live] at absent
      cases absent

-----------------------------------------------------------------------------------------
-- Every later handler either adds the occurrence to this ledger or retains its value
-----------------------------------------------------------------------------------------

/-- A buffered value with a surviving contributor is published or retained after replay.
Witness: compose the stored-value clauses of the same per-handler ledger. Permanent
registration transports endpoint liveness backward; take/drop membership embeds each
local publication into the full list without comparing or relabelling equal payloads.
-/
theorem State.ReplayClosuresCovered.conserves {queue : State} {work events published}
    (covered : queue.ReplayClosuresCovered events published)
    (live : queue.LiveGroupsRegistered) (registered : queue.TaskGroupsRegistered)
    (started : queue.StartedTasksRegistered)
    (matching : ∀ event ∈ events, event.MatchesWork work)
    : queue.StoredValuesConserved
        (published.take
          ((queue.rawEventReplay events).2.flatMap WorkQueueEvent.objectValues).length)
        (queue.replayGraphEvents events) := by
  induction events generalizing queue published with
  | nil => exact fun _ _ _ found _ _ => Or.inr found
  | cons event rest ih =>
      intro occurrence node value found stored survivor
      obtain ⟨contributor, contributes, owner, survives⟩ := survivor
      have next := queue.handleGraphEvent_registration live registered event
        (matching event List.mem_cons_self)
      have known := State.taskNode?_some found
      have recorded := registered node.task (started node known.1) contributor.key
        (List.mem_map.mpr ⟨contributor, contributes, rfl⟩)
      obtain ⟨currentOwner, currentLive⟩ := State.replayGraphEvents_live_registered
        (next.2.2 recorded) rest survives
      rcases covered.2.2.1 occurrence node value found stored
          ⟨contributor, contributes, currentOwner, currentLive⟩ with now | retained
      · apply Or.inl
        rw [State.rawEventReplay_cons, List.flatMap_append, List.length_append, List.take_add]
        exact List.mem_append_left _ now
      · have remaining := ih covered.tail next.1 next.2.1
          (started.handleGraphEvent event)
          (fun later member => matching later (List.mem_cons_of_mem _ member))
        rcases remaining occurrence node value retained stored
            ⟨contributor, contributes, owner, survives⟩ with later | still
        · apply Or.inl
          rw [State.rawEventReplay_cons, List.flatMap_append, List.length_append, List.take_add]
          exact List.mem_append_right _ later
        · exact Or.inr still

/-- A replay certificate restricts to earlier inputs, leaving later labels unused.
Witness: retain each prefix handler's certificates and truncate only the recursion.
The conservation theorem still bounds publication by the shorter replay's actual count.
-/
theorem State.ReplayClosuresCovered.prefix {queue : State} {published}
    (before after : List GraphEvent)
    (covered : queue.ReplayClosuresCovered (before ++ after) published)
    : queue.ReplayClosuresCovered before published := by
  induction before generalizing queue published with
  | nil => trivial
  | cons event rest ih =>
      exact ⟨covered.1, covered.2.1, covered.2.2.1, covered.2.2.2.1,
        covered.2.2.2.2.1, covered.2.2.2.2.2.1, covered.2.2.2.2.2.2.1,
        covered.2.2.2.2.2.2.2.1, covered.2.2.2.2.2.2.2.2.1, ih covered.tail⟩

/-- Removing earlier handlers leaves the actual intermediate queue and remaining labels.
Witness: add exact handler output counts while composing the ledger drops and state fold.
-/
theorem State.ReplayClosuresCovered.afterPrefix {queue : State} {published}
    (before after : List GraphEvent)
    (covered : queue.ReplayClosuresCovered (before ++ after) published)
    : (queue.replayGraphEvents before).ReplayClosuresCovered after
        (published.drop
          ((queue.rawEventReplay before).2.flatMap
            WorkQueueEvent.objectValues).length) := by
  induction before generalizing queue published with
  | nil => exact covered
  | cons event rest ih =>
      have later := ih covered.tail
      simpa only [List.cons_append, State.replayGraphEvents, List.foldl_cons,
        State.rawEventReplay_cons, List.flatMap_append, List.length_append,
        List.drop_drop] using later

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
