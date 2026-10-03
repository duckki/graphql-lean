import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RegionRegistration

/-! Fresh stream-item regions supply sequential registration availability. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- A fresh item has never-registered contributor refs
-----------------------------------------------------------------------------------------

/-- Every immediate group of a fresh item has an unregistered ref.
Witness: generated region separation excludes all previously exposed regions, while
registration provenance places every registered ref in one of those regions. -/
theorem State.RegionInventory.streamItem_groupsFresh {queue : State}
    {work seen stream items} (inventory : queue.RegionInventory work seen)
    (generated : ExecutedWork work)
    (matching : (GraphEvent.streamItems stream items).MatchesWork work)
    {item : StreamItem} (member : item ∈ items) (fresh : item.occurrence ∉ seen)
    : ∀ group ∈ item.work.groups, group.node.ref ∉ queue.registeredGroups := by
  obtain ⟨children, address, producer, owners, located, lowering, region⟩ :=
    matching.streamItem_region member
  intro group included registered
  rw [lowering] at included
  exact streamRegion_unexposed generated.regionsSeparated region fresh
    (workFromSpec_group_rootRef children address included)
    (inventory.registered_exposed registered)

/-- Every healthy contributor needed by a fresh item is available for registration.
Witness: immediate lowering contains each contributor group, whose ref is unregistered.
The result does not depend on the failure ledger or on whether the contributor is healthy.
-/
theorem State.RegionInventory.streamItem_available {queue : State}
    {work seen stream items failed}
    (inventory : queue.RegionInventory work seen) (generated : ExecutedWork work)
    (matching : (GraphEvent.streamItems stream items).MatchesWork work)
    {item : StreamItem} (member : item ∈ items) (fresh : item.occurrence ∉ seen)
    : queue.ChildGroupsAvailable work failed item.work := by
  intro task registered ref contributes _
  obtain ⟨group, included, same⟩ :=
    matching.streamItem_childTasksCovered member task registered ref contributes
  exact .inr (same ▸ inventory.streamItem_groupsFresh generated matching member fresh
    group included)

-----------------------------------------------------------------------------------------
-- Freshness holds at each intermediate state inside a multi-item event
-----------------------------------------------------------------------------------------

/-- A fresh, duplicate-free item batch has available contributors at every integration.
Witness: induct over the actual sequential integration states, exposing each item's
region only after proving that item's availability. -/
theorem State.RegionInventory.streamItems_available {queue : State}
    {work seen stream items failed} (inventory : queue.RegionInventory work seen)
    (generated : ExecutedWork work)
    (matching : (GraphEvent.streamItems stream items).MatchesWork work)
    (unique : (items.map StreamItem.occurrence).Nodup)
    (fresh : ∀ item ∈ items, item.occurrence ∉ seen)
    : queue.StreamRegistrationsAvailable work failed items := by
  induction items generalizing queue seen with
  | nil => trivial
  | cons item rest ih =>
      have unique := List.nodup_cons.mp unique
      refine ⟨inventory.streamItem_available generated matching List.mem_cons_self
        (fresh item List.mem_cons_self), ?_⟩
      apply ih (inventory.integrateStreamItem matching List.mem_cons_self)
        (fun next member => matching next (List.mem_cons_of_mem item member)) unique.2
      intro next member recorded
      rcases List.mem_cons.mp recorded with same | earlier
      · exact unique.1 (same ▸ List.mem_map_of_mem member)
      · exact fresh next (List.mem_cons_of_mem item member) earlier

/-- Matching fresh stream items are available after arbitrary legal source replay.
Witness: the replay region inventory and the source's within/across-event freshness
clauses. No pending-count, root-health, or registration-availability premise is needed. -/
theorem createWorkQueue_replay_streamRegistrationsAvailable {work : Execution.Work}
    (generated : ExecutedWork work) {before : List GraphEvent}
    (valid : ValidGraphEvents work before) {stream items failed}
    (matching : (GraphEvent.streamItems stream items).MatchesWork work)
    (fresh : (GraphEvent.streamItems stream items).Fresh before)
    : ((State.initialize (Work.fromExecution work)).replayGraphEvents
        before).StreamRegistrationsAvailable
        work failed items := by
  apply (createWorkQueue_replay_regionInventory valid).streamItems_available generated
    matching fresh.1
  intro item member
  exact fresh.2.2.1 item.occurrence (List.mem_map_of_mem member)

/-- Stream registration availability holds at every event boundary in a valid replay.
Witness: prefix induction and the local fresh-item theorem, before processing that event.
-/
theorem createWorkQueue_replay_streamRegistrationsAvailableAt {work : Execution.Work}
    (generated : ExecutedWork work) {events : List GraphEvent}
    (valid : ValidGraphEvents work events)
    : ∀ before stream items,
        (before ++ [.streamItems stream items]).IsPrefix events
        → ((State.initialize (Work.fromExecution work)).replayGraphEvents
            before).StreamRegistrationsAvailable
            work (GraphEvent.failureSettlements before) items := by
  induction valid with
  | nil =>
      intro before stream items earlier
      have empty := List.eq_nil_of_prefix_nil earlier
      simp at empty
  | @append prior event validPrior matching fresh ready ih =>
      intro before stream items earlier
      rcases List.prefix_concat_iff.mp earlier with same | shorter
      · have parts := List.append_inj' same rfl
        have sameBefore := parts.1
        have sameEvent := List.singleton_inj.mp parts.2
        subst before event
        exact createWorkQueue_replay_streamRegistrationsAvailable generated validPrior
          matching fresh
      · exact ih before stream items shorter

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
