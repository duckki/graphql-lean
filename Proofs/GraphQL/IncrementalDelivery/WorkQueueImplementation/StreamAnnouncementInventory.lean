import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupStreamNoticeUniqueness

/-! Concrete stream announcements consume links retained by their producing tasks. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Announcement history and unreleased stored links
-----------------------------------------------------------------------------------------

/-- `announced` is a distinct registered history, disjoint from every stored child list.
This proof-only inventory tracks executable registration and consumption, not admission.
-/
structure State.StreamAnnouncementInventory (queue : State) (announced : Keys)
    : Prop where
  /-- An announced key occurs only once in the retained history. -/
  unique : announced.Nodup
  /-- Every earlier announcement remains in the permanent descriptor registry. -/
  registered : announced.Subset (queue.streams.map (fun stream => stream.node.key))
  /-- Stored child lists remain distinct and registered. -/
  stored : queue.ChildStreamInventory
  /-- A stored child link has not been consumed by an earlier announcement. -/
  unreleased : ∀ node ∈ queue.taskNodes, ∀ key ∈ node.childStreams, key ∉ announced

/-- A registry extension retaining old or empty child lists preserves announcement state.
Witness: original link provenance transports both stored uniqueness and nonannouncement.
-/
theorem State.StreamAnnouncementInventory.of_frame {before after : State}
    {announced : Keys} (inventory : before.StreamAnnouncementInventory announced)
    (registered : before.streams.Subset after.streams)
    (retained
      : ∀ node ∈ after.taskNodes,
          node.childStreams = []
          ∨ ∃ old ∈ before.taskNodes, node.childStreams = old.childStreams)
    : after.StreamAnnouncementInventory announced := by
  refine ⟨inventory.unique, inventory.registered.trans (List.map_subset _ registered),
    inventory.stored.of_frame registered retained, ?_⟩
  intro node member key linked
  rcases retained node member with empty | ⟨old, included, same⟩
  · simp [empty] at linked
  · exact inventory.unreleased old included key (same ▸ linked)

/-- Group registration leaves announcement history and stored stream links unchanged.
Witness: exact task-map and registry projections.
-/
theorem State.StreamAnnouncementInventory.addGroups {queue : State} {announced : Keys}
    (inventory : queue.StreamAnnouncementInventory announced) (groups : List Group)
    : (queue.addGroups groups).1.StreamAnnouncementInventory announced := by
  apply inventory.of_frame
  · rw [State.addGroups_streams]; exact List.Subset.refl _
  · intro node member
    rw [State.addGroups_taskNodes] at member
    exact .inr ⟨node, member, rfl⟩

/-- Task registration keeps old child links or adds an empty child list.
Witness: the executable old-or-new node characterization.
-/
theorem State.StreamAnnouncementInventory.addTask {queue : State} {announced : Keys}
    (inventory : queue.StreamAnnouncementInventory announced) (task : Task)
    : (queue.addTask task).StreamAnnouncementInventory announced := by
  apply inventory.of_frame
  · rw [State.addTask_streams]; exact List.Subset.refl _
  · intro node member
    rcases queue.addTask_startedOldOrNew task member with old | new
    · exact .inr ⟨node, old, rfl⟩
    · exact .inl (new ▸ rfl)

/-- Stream registration either announces fresh roots or retains fresh unannounced links.
Witness: actual selection excludes the entire old registry; old announcements and old
stored links are registered there. Task attachment returns no immediate announcements.
-/
theorem State.StreamAnnouncementInventory.addStreams {queue : State} {announced : Keys}
    (inventory : queue.StreamAnnouncementInventory announced) (streams : List Stream)
    (parent : Option Occurrence)
    : (queue.addStreams streams parent).1.StreamAnnouncementInventory
        (announced
          ++ (queue.addStreams streams parent).2.map Execution.DeliveryNode.key) := by
  have fresh := queue.addStreams_notices_fresh streams parent
  have registry := queue.addStreams_registered streams parent
  have unique : (announced ++ (queue.addStreams streams parent).2.map
      Execution.DeliveryNode.key).Nodup := by
    refine List.nodup_append.mpr ⟨inventory.unique, fresh.1, ?_⟩
    intro key earlier next member same
    obtain ⟨node, included, equal⟩ := List.mem_map.mp member
    exact fresh.2 node included ((same.trans equal.symm) ▸ inventory.registered earlier)
  refine ⟨unique, ?_, inventory.stored.addStreams streams parent, ?_⟩
  · intro key member
    rcases List.mem_append.mp member with old | new
    · exact (List.map_subset _ registry.1) (inventory.registered old)
    · obtain ⟨node, noticed, same⟩ := List.mem_map.mp new
      obtain ⟨stream, registered, equal⟩ := List.mem_map.mp (registry.2 noticed)
      exact List.mem_map.mpr ⟨stream, registered,
        (congrArg Execution.DeliveryNode.key equal).trans same⟩
  · let selected : List Stream := streams.foldl (fun chosen stream =>
      if (queue.stream? stream.node.key).isSome
          || chosen.any (fun old => old.node.key == stream.node.key) then chosen
      else chosen ++ [stream]) []
    have selectedFresh := queue.addStreams_selection_fresh streams
    cases parent with
    | none =>
        intro node member key linked noticed
        rcases List.mem_append.mp noticed with old | new
        · exact inventory.unreleased node member key linked old
        · obtain ⟨stream, included, same⟩ := List.mem_map.mp new
          exact (queue.addStreams_notices_fresh streams none).2 stream included
            (same ▸ (inventory.stored node member).2 linked)
    | some occurrence =>
        simp only [State.addStreams]
        split
        · simpa only [List.map_nil, List.append_nil] using inventory.unreleased
        · rename_i updated found
          intro node member key linked noticed
          have earlier : key ∈ announced := by simpa using noticed
          obtain ⟨old, included, equal⟩ := List.mem_map.mp member
          split at equal
          · subst node
            rcases List.mem_append.mp linked with oldLink | newLink
            · exact inventory.unreleased updated (State.taskNode?_some found).1 key
                oldLink earlier
            · obtain ⟨stream, selected, same⟩ := List.mem_map.mp newLink
              exact selectedFresh.2 stream selected (same ▸ inventory.registered earlier)
          · subst node
            exact inventory.unreleased old included key linked earlier

private theorem fold_preserves {α β : Type} (property : α → Prop) (step : α → β → α)
    (preserved : ∀ current item, property current → property (step current item))
    (items : List β) (current : α) (prior : property current)
    : property (items.foldl step current) := by
  induction items generalizing current with
  | nil => exact prior
  | cons item rest ih => exact ih _ (preserved current item prior)

/-- Full child-work integration accounts for exactly its immediate stream announcements.
Witness: groups and tasks retain existing links, then stream selection consumes only fresh
root keys or attaches fresh unannounced children to their producer.
-/
theorem State.StreamAnnouncementInventory.maybeIntegrateWork {queue : State}
    {announced : Keys} (inventory : queue.StreamAnnouncementInventory announced)
    (work : Work) (parent : Option Occurrence := none)
    : (queue.maybeIntegrateWork work parent).1.StreamAnnouncementInventory
        (announced
          ++ (queue.maybeIntegrateWork work parent).2.newStreams.map
              Execution.DeliveryNode.key) := by
  have tasked := fold_preserves (fun current => current.StreamAnnouncementInventory announced)
    State.addTask (fun _ task prior => prior.addTask task) work.tasks _
    (inventory.addGroups work.groups)
  exact tasked.addStreams work.streams parent

-----------------------------------------------------------------------------------------
-- A flush consumes selected producers' links exactly once
-----------------------------------------------------------------------------------------

/-- Group release announces previously unannounced streams and removes their stored links.
Witness: selected producer occurrences are removed from the residual task map. Generated
producer uniqueness forbids another retained task from holding any released stream key.
-/
theorem State.StreamAnnouncementInventory.finishGroupSuccess {queue : State}
    {work : Execution.Work} {announced : Keys}
    (inventory : queue.StreamAnnouncementInventory announced)
    (matching : queue.ChildStreamsMatchWork work) (generated : ExecutedWork work)
    (group : GroupNode)
    : (queue.finishGroupSuccess group).1.StreamAnnouncementInventory
        (announced
          ++ (queue.finishGroupSuccess group).2.2.newStreams.map
              Execution.DeliveryNode.key) := by
  obtain ⟨selected, _, known, _, retained, absent, released⟩ :=
    queue.finishGroupSuccess_selection group
  refine ⟨?_, ?_, inventory.stored.finishGroupSuccess group, ?_⟩
  · refine List.nodup_append.mpr ⟨inventory.unique,
      inventory.stored.finishGroupSuccess_streamKeys_nodup matching generated group, ?_⟩
    intro key earlier other member same
    obtain ⟨stream, noticed, equal⟩ := List.mem_map.mp member
    obtain ⟨producer, chosen, linked⟩ := released stream noticed
    exact inventory.unreleased producer (known producer chosen).1 stream.key linked
      ((same.trans equal.symm) ▸ earlier)
  · intro key member
    rw [State.finishGroupSuccess_streams]
    rcases List.mem_append.mp member with old | new
    · exact inventory.registered old
    · obtain ⟨stream, noticed, same⟩ := List.mem_map.mp new
      have registered := queue.finishGroupSuccess_streams_registered group noticed
      rw [State.finishGroupSuccess_streams] at registered
      obtain ⟨descriptor, included, equal⟩ := List.mem_map.mp registered
      exact List.mem_map.mpr ⟨descriptor, included,
        (congrArg Execution.DeliveryNode.key equal).trans same⟩
  · intro node member key linked noticed
    rcases List.mem_append.mp noticed with old | new
    · exact inventory.unreleased node (retained member) key linked old
    · obtain ⟨stream, included, same⟩ := List.mem_map.mp new
      obtain ⟨producer, chosen, producerLink⟩ := released stream included
      have equal := matching.shared_key_producer generated (retained member)
        (known producer chosen).1 linked (same ▸ producerLink)
      exact absent producer chosen node member equal

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
