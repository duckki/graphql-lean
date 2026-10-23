import Proofs.GraphQL.IncrementalDelivery.Correctness.StreamNoticeSupport
import Proofs.GraphQL.IncrementalDelivery.Correctness.ReportingNoticeCoverage

/-! Select covering group notices and fully supported stream notices on real carriers. -/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Semantics
open Semantics.GeneralScheduling WorkQueueSemantics

/-- A frontier may cover every eligible group while delaying unsupported stream notices. -/
theorem reporting_announcements_exists
    {ancestry roles work initial matching events failures}
    (roleCoherent : RefRoles.WorkRoles roles work)
    (allocated : (streamAllocationRefs work).Nodup)
    : ∃ groups streams,
        Announcements work initial matching events failures groups streams
        ∧ (∀ stream ∈ streams,
            ∃ dependencies producer,
              NodeAt work stream .stream dependencies producer
              ∧ StreamDependencySupport ancestry work initial matching events failures
                  dependencies)
        ∧ (∀ node dependencies producer,
            NodeAt work node .group dependencies producer
            → CanAnnounce work initial matching events failures node .group dependencies
                producer
            → node.ref ∈ (groups ++ streams).map DeliveryNode.ref)
        ∧ ∀ node dependencies producer,
            NodeAt work node .stream dependencies producer
            → CanAnnounce work initial matching events failures node .stream dependencies
                producer
            → StreamDependencySupport ancestry work initial matching events failures
                dependencies
            → node.ref ∈ (groups ++ streams).map DeliveryNode.ref := by
  classical
  obtain ⟨groups, streams, notices, covers⟩ := announcements_covering_exists work initial
    matching events failures
  let supported (stream : DeliveryNode) : Prop :=
    ∃ dependencies producer, NodeAt work stream .stream dependencies producer
      ∧ StreamDependencySupport ancestry work initial matching events failures dependencies
  let kept := streams.filter (fun stream => decide (supported stream))
  have subset : kept.Sublist streams := List.filter_sublist
  have retained : Announcements work initial matching events failures groups kept := by
    refine ⟨?_, notices.2.1, ?_⟩
    · exact ((List.Sublist.refl groups).append subset |>.map DeliveryNode.ref).nodup notices.1
    · intro stream member
      exact notices.2.2 stream (subset.subset member)
  refine ⟨groups, kept, retained, ?_, ?_, ?_⟩
  · intro stream member
    exact of_decide_eq_true (List.mem_filter.mp member).2
  · intro node dependencies producer known eligible
    obtain ⟨notice, member, same⟩ := List.mem_map.mp
      (covers node .group dependencies producer known eligible)
    rcases List.mem_append.mp member with group | stream
    · exact List.mem_map.mpr ⟨notice, List.mem_append_left _ group, same⟩
    · obtain ⟨parents, birth, descriptor, _⟩ := notices.2.2 notice stream
      exact False.elim (stream_group_refs_distinct roleCoherent descriptor known same)
  · intro node dependencies producer known eligible full
    obtain ⟨notice, member, same⟩ := List.mem_map.mp
      (covers node .stream dependencies producer known eligible)
    rcases List.mem_append.mp member with group | stream
    · exact List.mem_map.mpr ⟨notice, List.mem_append_left _ group, same⟩
    · obtain ⟨parents, birth, descriptor, _⟩ := notices.2.2 notice stream
      have equal := (streamMetadata_unique allocated descriptor known same).1
      have support : supported notice := ⟨parents, birth, descriptor, equal.symm ▸ full⟩
      exact List.mem_map.mpr ⟨notice, List.mem_append_right _ (List.mem_filter.mpr
        ⟨stream, by simpa only [decide_eq_true_eq] using support⟩), same⟩

/-- Supported-frontier coverage survives attaching the selected notices to a carrier. -/
theorem ReportingNoticesCovered.carrier
    {ancestry work initial matching events failures plain actual}
    {groups streams : List DeliveryNode}
    (noNotices : eventPending plain = [])
    (notices : eventPending actual = (groups ++ streams).map DeliveryNode.ref)
    (sameValue : IsValue plain ↔ IsValue actual)
    (sameCompleted : eventCompleted plain = eventCompleted actual)
    (groupCover
      : ∀ node dependencies producer,
          NodeAt work node .group dependencies producer
          → CanAnnounce work initial matching (events ++ [plain]) failures node .group
              dependencies producer
          → node.ref ∈ (groups ++ streams).map DeliveryNode.ref)
    (streamCover
      : ∀ node dependencies producer,
          NodeAt work node .stream dependencies producer
          → CanAnnounce work initial matching (events ++ [plain]) failures node .stream
              dependencies producer
          → StreamDependencySupport ancestry work initial matching (events ++ [plain])
              failures dependencies
          → node.ref ∈ (groups ++ streams).map DeliveryNode.ref)
    : ReportingNoticesCovered ancestry work initial matching (events ++ [actual])
        failures := by
  have causal := causality_carrier_eq (work := work) (matching := matching)
    (events := events) (failures := failures) sameValue
  have publications : ∀ occurrence, Published matching (events ++ [plain]) occurrence
      ↔ Published matching (events ++ [actual]) occurrence := by
    intro occurrence
    simp only [published_append_singleton_iff, sameValue]
  have earlier : (announcedRefs initial (events ++ [plain])).Subset
      (announcedRefs initial (events ++ [actual])) := by
    simp only [announcedRefs, pendingRefs, List.flatMap_append, List.flatMap_cons,
      List.flatMap_nil, List.append_nil, noNotices]
    intro ref member
    simpa only [List.append_assoc] using List.mem_append_left (eventPending actual) member
  have completions : completedRefs (events ++ [actual]) = completedRefs (events ++ [plain]) := by
    simp only [completedRefs, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      sameCompleted]
  have dependency {ref}
      (satisfied : DependencySatisfied work initial matching (events ++ [actual]) failures ref)
      : DependencySatisfied work initial matching (events ++ [plain]) failures ref := by
    refine ⟨by simpa only [causal.1] using satisfied.1, ?_⟩
    rcases satisfied.2 with absent | closed | ⟨fresh, accounted⟩
    · exact Or.inl absent
    · exact Or.inr (Or.inl (completions ▸ closed))
    · refine Or.inr (Or.inr ⟨fun member => fresh (earlier member), ?_⟩)
      simpa only [NodeAccounted, TaskAccounted, publications, causal.2] using accounted
  have eligible {node kind dependencies producer}
      (notice : CanAnnounce work initial matching (events ++ [actual]) failures node kind
        dependencies producer)
      : CanAnnounce work initial matching (events ++ [plain]) failures node kind
          dependencies producer :=
    notice.fewer_notices earlier publications causal
      (by rw [completions]; exact List.Subset.refl _)
      (by simp only [List.length_append, List.length_singleton]; exact List.Subset.refl _)
  have announced {node : DeliveryNode}
      (member : node.ref ∈ (groups ++ streams).map DeliveryNode.ref)
      : node.ref ∈ announcedRefs initial (events ++ [actual]) := by
    simpa only [announcedRefs, pendingRefs, List.flatMap_append, List.flatMap_cons,
      List.flatMap_nil, List.append_nil, List.append_assoc, notices]
      using List.mem_append_right (announcedRefs initial events) member
  have groupCovered : GroupNoticesCovered work initial matching (events ++ [actual])
      failures := by
    intro node dependencies producer known notice
    exact notice.1 (announced (groupCover node dependencies producer known (eligible notice)))
  refine ⟨?_, groupCovered⟩
  intro node kind dependencies producer known supported
  cases kind with
  | group => exact groupCovered node dependencies producer known supported.1
  | stream =>
      apply supported.1.1
      apply announced
      apply streamCover node dependencies producer known (eligible supported.1)
      rcases supported.2.2 rfl with empty | ⟨ref, member, satisfied, ancestors⟩
      · exact Or.inl empty
      · exact Or.inr ⟨ref, member, dependency satisfied,
          fun ancestor member => dependency (ancestors ancestor member)⟩

/-- Complete an accounted healthy group with the selected reporting frontier. -/
theorem Explains.complete_group_reporting
    {ancestry roles work groups streams events matching failures node dependencies birth}
    (roleCoherent : RefRoles.WorkRoles roles work)
    (allocated : (streamAllocationRefs work).Nodup)
    (explained : Explains work groups streams events matching failures)
    (known : NodeAt work node .group dependencies birth)
    (opened : Open ((groups ++ streams).map DeliveryNode.ref) events node.ref)
    (healthy : ¬NodeFailed work matching events failures node.ref)
    (accounted : NodeAccounted work matching events failures node.ref)
    : ∃ newGroups newStreams,
        Explains work groups streams (events ++ [.groupSuccess node newGroups newStreams])
          matching failures
        ∧ ReportingNoticesCovered ancestry work ((groups ++ streams).map DeliveryNode.ref)
            matching (events ++ [.groupSuccess node newGroups newStreams]) failures
        ∧ CarriedStreamSupport ancestry work ((groups ++ streams).map DeliveryNode.ref)
            matching events failures (.groupSuccess node newGroups newStreams) := by
  obtain ⟨newGroups, newStreams, notices, supports, groupCover, streamCover⟩ :=
    reporting_announcements_exists (ancestry := ancestry) (initial := (groups ++ streams).map
      DeliveryNode.ref) (matching := matching) (events := events ++ [.groupSuccess node [] []])
      (failures := failures) roleCoherent allocated
  refine ⟨newGroups, newStreams, explained.append_event ?_, ?_, supports⟩
  · simp only [EventAllowed, explained.2.1.filter_eq_self (Nat.le_refl _)]
    exact ⟨⟨dependencies, birth, known⟩, opened, healthy, accounted, notices⟩
  · exact ReportingNoticesCovered.carrier (plain := .groupSuccess node [] [])
      rfl rfl Iff.rfl rfl groupCover streamCover

/-- Publish one stream item with fully supported new stream notices. -/
theorem Explains.publish_item_reporting
    {ancestry roles work groups streams events matching failures occurrence owners
      producer node item errors}
    (roleCoherent : RefRoles.WorkRoles roles work)
    (allocated : (streamAllocationRefs work).Nodup)
    (explained : Explains work groups streams events matching failures)
    (known : TaskAt work occurrence owners producer (.item node (.ok (item, errors))))
    (ready : CanPublish work matching events failures occurrence producer)
    (owner
      : PublicationOwner work ((groups ++ streams).map DeliveryNode.ref) matching events
          failures owners node)
    : ∃ newGroups newStreams,
        Explains work groups streams
          (events ++ [.streamValues node [{ item, errors }] newGroups newStreams])
          (matchNext matching events.length occurrence) failures
        ∧ ReportingNoticesCovered ancestry work ((groups ++ streams).map DeliveryNode.ref)
            (matchNext matching events.length occurrence)
            (events ++ [.streamValues node [{ item, errors }] newGroups newStreams])
            failures
        ∧ CarriedStreamSupport ancestry work ((groups ++ streams).map DeliveryNode.ref)
            (matchNext matching events.length occurrence) events failures
            (.streamValues node [{ item, errors }] newGroups newStreams) := by
  obtain ⟨newGroups, newStreams, notices, supports, groupCover, streamCover⟩ :=
    reporting_announcements_exists (ancestry := ancestry)
      (initial := (groups ++ streams).map DeliveryNode.ref)
      (matching := matchNext matching events.length occurrence)
      (events := events ++ [.streamValues node [{ item, errors }] [] []])
      (failures := failures) roleCoherent allocated
  have same := fun index before => matchNext_before matching occurrence
    (index := events.length) (position := index) before
  refine ⟨newGroups, newStreams, (explained.change_matching same).append_event ?_, ?_, supports⟩
  · simp only [EventAllowed, explained.2.1.filter_eq_self (Nat.le_refl _)]
    refine ⟨owners, producer, { item, errors }, rfl, ?_, ?_,
      owner_matching_eq same ▸ owner, notices⟩
    · simpa only [matchNext, ↓reduceIte] using known
    · simpa only [matchNext, ↓reduceIte] using (canPublish_matching_eq same ▸ ready)
  · exact ReportingNoticesCovered.carrier (plain := .streamValues node [{ item, errors }] [] [])
      rfl rfl Iff.rfl rfl groupCover streamCover

end GraphQL.IncrementalDelivery.Correctness
