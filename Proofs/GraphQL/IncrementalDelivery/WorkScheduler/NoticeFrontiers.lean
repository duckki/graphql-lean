import Proofs.GraphQL.IncrementalDelivery.WorkScheduler.FiniteHistories

/-! Complete eligible notice frontiers exist without choosing later task outcomes.
These finite witnesses strengthen chosen frontiers, not the public admission contract.
-/

namespace GraphQL.IncrementalDelivery.WorkScheduler
open GraphQL.IncrementalDelivery.Execution

-----------------------------------------------------------------------------------------
-- Extending a frontier without changing its observation prefix
-----------------------------------------------------------------------------------------

/-- Add one eligible group whose key is absent from this chosen frontier. Witness:
fresh-key list insertion, retaining the same observed prefix for every eligibility check.
-/
theorem Announcements.cons_group
    {work initial matching events failed groups streams node dependencies birth}
    (announced : Announcements work initial matching events failed groups streams)
    (known : NodeAt work node .group dependencies birth)
    (eligible
      : CanAnnounce work initial matching events failed node .group dependencies birth)
    (fresh : node.key ∉ (groups ++ streams).map DeliveryNode.key)
    : Announcements work initial matching events failed (node :: groups) streams := by
  refine ⟨
    by
      simpa only [List.cons_append, List.map_cons, List.nodup_cons]
        using And.intro fresh announced.1,
    ?_,
    announced.2.2
  ⟩
  intro other member
  rcases List.mem_cons.mp member with rfl | member
  · exact ⟨dependencies, birth, known, eligible⟩
  · exact announced.2.1 other member

/-- Add one eligible stream with a new frontier key. Witness: insert its unique key
beside the existing stream entries; group/stream list ordering does not affect admission.
-/
theorem Announcements.cons_stream
    {work initial matching events failed groups streams node dependencies birth}
    (announced : Announcements work initial matching events failed groups streams)
    (known : NodeAt work node .stream dependencies birth)
    (eligible
      : CanAnnounce work initial matching events failed node .stream dependencies birth)
    (fresh : node.key ∉ (groups ++ streams).map DeliveryNode.key)
    : Announcements work initial matching events failed groups (node :: streams) := by
  refine ⟨?_, announced.2.1, ?_⟩
  · have unique := List.nodup_cons.mpr (And.intro fresh announced.1)
    have perm : ((groups ++ node :: streams).map DeliveryNode.key).Perm
        (node.key :: (groups ++ streams).map DeliveryNode.key) :=
      List.perm_middle.map DeliveryNode.key
    exact perm.symm.nodup unique
  · intro other member
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨dependencies, birth, known, eligible⟩
    · exact announced.2.2 other member

-----------------------------------------------------------------------------------------
-- A frontier may include every currently eligible key
-----------------------------------------------------------------------------------------

/-- A notice frontier covering all eligible node keys exists for any finite raw work.
Witness: inspect the finite token inventory, choosing at most one eligible descriptor per
key. The frontier can be empty; repeated metadata and owner ties remain permitted.
-/
theorem announcements_covering_exists (work : Work) (initial : Keys)
    (matching : PublicationMatching) (events : List WorkEvent) (failed : List Occurrence)
    : ∃ groups streams,
        Announcements work initial matching events failed groups streams
        ∧ ∀ node kind dependencies birth,
            NodeAt work node kind dependencies birth
            → CanAnnounce work initial matching events failed node kind dependencies birth
            → node.key ∈ (groups ++ streams).map DeliveryNode.key := by
  classical
  have cover (tokens : List ObservationToken) : ∃ groups streams,
      Announcements work initial matching events failed groups streams
      ∧ ∀ node kind dependencies birth,
          NodeAt work node kind dependencies birth
          → CanAnnounce work initial matching events failed node kind dependencies birth
          → .inr node.key ∈ tokens
          → node.key ∈ (groups ++ streams).map DeliveryNode.key := by
    induction tokens with
    | nil => exact ⟨[], [], by simp [Announcements], by simp⟩
    | cons token tokens ih =>
        obtain ⟨groups, streams, announced, covers⟩ := ih
        cases token with
        | inl occurrence =>
            refine ⟨groups, streams, announced, ?_⟩
            intro node kind dependencies birth known eligible member
            apply covers node kind dependencies birth known eligible
            simpa only [List.mem_cons, reduceCtorEq, false_or] using member
        | inr key =>
            by_cases chosen : key ∈ (groups ++ streams).map DeliveryNode.key
            · refine ⟨groups, streams, announced, ?_⟩
              intro node kind dependencies birth known eligible member
              rcases List.mem_cons.mp member with equal | member
              · have same := Sum.inr.inj equal
                exact same ▸ chosen
              · exact covers node kind dependencies birth known eligible member
            · by_cases possible :
                ∃ node kind dependencies birth,
                  NodeAt work node kind dependencies birth
                  ∧ CanAnnounce work initial matching events failed node kind dependencies
                      birth
                  ∧ node.key = key
              · obtain ⟨node, kind, dependencies, birth, known, eligible, rfl⟩ := possible
                cases kind with
                | group =>
                    refine ⟨node :: groups, streams,
                      announced.cons_group known eligible chosen, ?_⟩
                    intro other kind dependencies birth known eligible member
                    rcases List.mem_cons.mp member with same | member
                    · simp only [List.cons_append, List.map_cons, List.mem_cons]
                      exact Or.inl (Sum.inr.inj same)
                    · exact List.mem_cons_of_mem _
                        (covers other kind dependencies birth known eligible member)
                | stream =>
                    refine ⟨groups, node :: streams,
                      announced.cons_stream known eligible chosen, ?_⟩
                    intro other kind dependencies birth known eligible member
                    have oldOrNew : other.key = node.key
                        ∨ other.key ∈ (groups ++ streams).map DeliveryNode.key := by
                      rcases List.mem_cons.mp member with same | member
                      · exact Or.inl (Sum.inr.inj same)
                      · exact Or.inr (covers other kind dependencies birth known eligible member)
                    simpa only [List.map_append, List.map_cons, List.mem_append,
                      List.mem_cons, or_left_comm]
                      using oldOrNew
              · refine ⟨groups, streams, announced, ?_⟩
                intro node kind dependencies birth known eligible member
                rcases List.mem_cons.mp member with same | member
                · exact False.elim (possible ⟨node, kind, dependencies, birth, known, eligible,
                    Sum.inr.inj same⟩)
                · exact covers node kind dependencies birth known eligible member
  obtain ⟨groups, streams, announced, covers⟩ := cover (observationTokens [] work)
  exact ⟨groups, streams, announced, fun node kind dependencies birth known eligible =>
    covers node kind dependencies birth known eligible known.observationToken⟩

/-- Whenever initialization is possible, it can announce every initially eligible key.
Witness: the complete eligible frontier contains a key from the original nonempty one.
This makes no assertion about the existence of a complete future run.
-/
theorem Initializes.covering_exists {work groups streams}
    (initialized : Initializes work groups streams)
    : ∃ allGroups allStreams,
        Initializes work allGroups allStreams
        ∧ ∀ node kind dependencies birth,
            NodeAt work node kind dependencies birth
            → CanAnnounce work [] (fun _ => .executionGroup []) [] [] node kind
                dependencies birth
            → node.key ∈ (allGroups ++ allStreams).map DeliveryNode.key := by
  obtain ⟨allGroups, allStreams, announced, covers⟩ :=
    announcements_covering_exists work [] (fun _ => .executionGroup []) [] []
  refine ⟨allGroups, allStreams, ⟨announced, ?_⟩, covers⟩
  intro empty
  obtain ⟨node, member⟩ := List.exists_mem_of_ne_nil _ initialized.2
  rcases List.mem_append.mp member with inGroups | inStreams
  · obtain ⟨dependencies, birth, known, eligible⟩ := initialized.1.2.1 node inGroups
    have member := covers node .group dependencies birth known eligible
    simp only [empty, List.map_nil, List.not_mem_nil] at member
  · obtain ⟨dependencies, birth, known, eligible⟩ := initialized.1.2.2 node inStreams
    have member := covers node .stream dependencies birth known eligible
    simp only [empty, List.map_nil, List.not_mem_nil] at member

-----------------------------------------------------------------------------------------
-- The two notice-bearing event forms can carry a complete frontier
-----------------------------------------------------------------------------------------

/-- A ready stream publication can announce every key eligible after publishing its item.
Witness: extend the matching at the new index, construct the complete eligible frontier,
and attach it to the actual stream-value event. No future observation is chosen.
-/
theorem Explains.publish_item_covering
    {work groups streams events matching failures occurrence owners producer node item
      errors}
    (explained : Explains work groups streams events matching failures)
    (known : TaskAt work occurrence owners producer (.item node (.ok (item, errors))))
    (ready
      : CanPublish work matching events (failedBefore failures events.length)
          occurrence producer)
    (selected
      : Owner work ((groups ++ streams).map DeliveryNode.key) events
          (failedBefore failures events.length) owners node)
    : ∃ newGroups newStreams,
        Explains work groups streams
          (events ++ [.streamValues node [{ item, errors }] newGroups newStreams])
          (matchNext matching events.length occurrence) failures
        ∧ ∀ child kind dependencies birth,
            NodeAt work child kind dependencies birth
            → CanAnnounce work ((groups ++ streams).map DeliveryNode.key)
                (matchNext matching events.length occurrence)
                (events ++ [.streamValues node [{ item, errors }] [] []])
                (failedBefore failures events.length) child kind dependencies birth
            → child.key ∈ (newGroups ++ newStreams).map DeliveryNode.key := by
  obtain ⟨newGroups, newStreams, notices, covers⟩ := announcements_covering_exists work
    ((groups ++ streams).map DeliveryNode.key)
    (matchNext matching events.length occurrence)
    (events ++ [.streamValues node [{ item, errors }] [] []])
    (failedBefore failures events.length)
  refine ⟨newGroups, newStreams, ?_, covers⟩
  have same := fun index before => matchNext_before matching occurrence
    (index := events.length) (position := index) before
  apply (explained.change_matching same).append_event
  refine ⟨owners, producer, item, errors, rfl, ?_, ?_, selected, notices⟩
  · simpa only [matchNext, ↓reduceIte] using known
  · simpa only [matchNext, ↓reduceIte] using (canPublish_matching_eq same ▸ ready)

/-- A healthy accounted group can close while announcing every newly eligible key.
Witness: compute eligibility after the plain closure, then attach its complete frontier
to the same group-success event. Other unfinished work does not need to be accounted for.
-/
theorem Explains.complete_group_covering
    {work groups streams events matching failures node dependencies birth}
    (explained : Explains work groups streams events matching failures)
    (known : NodeAt work node .group dependencies birth)
    (opened : Open ((groups ++ streams).map DeliveryNode.key) events node.key)
    (healthy : ¬NodeFailed work (failedBefore failures events.length) node.key)
    (accounted
      : NodeAccounted work matching events (failedBefore failures events.length) node.key)
    : ∃ newGroups newStreams,
        Explains work groups streams
          (events ++ [.groupSuccess node newGroups newStreams]) matching failures
        ∧ ∀ child kind dependencies birth,
            NodeAt work child kind dependencies birth
            → CanAnnounce work ((groups ++ streams).map DeliveryNode.key) matching
                (events ++ [.groupSuccess node [] []])
                (failedBefore failures events.length) child kind dependencies birth
            → child.key ∈ (newGroups ++ newStreams).map DeliveryNode.key := by
  obtain ⟨newGroups, newStreams, notices, covers⟩ := announcements_covering_exists work
    ((groups ++ streams).map DeliveryNode.key) matching
    (events ++ [.groupSuccess node [] []]) (failedBefore failures events.length)
  exact ⟨newGroups, newStreams,
    explained.append_event ⟨⟨dependencies, birth, known⟩, opened, healthy, accounted, notices⟩,
    covers⟩

end GraphQL.IncrementalDelivery.WorkScheduler
