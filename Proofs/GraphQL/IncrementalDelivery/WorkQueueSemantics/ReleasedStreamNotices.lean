import Proofs.GraphQL.IncrementalDelivery.WorkQueueSemantics.StreamNotices

/-! Notice carriers after deferred dependencies close. These are construction witnesses,
not additional premises on the public work-history relation.
-/

namespace GraphQL.IncrementalDelivery.WorkQueueSemantics
open GraphQL.IncrementalDelivery.Execution

-----------------------------------------------------------------------------------------
-- Streams whose deferred dependencies have already closed
-----------------------------------------------------------------------------------------

/-- Every healthy stream with a published producer has already been announced.
Unlike dependency-free coverage, this witness also includes streams released by deferred
work.
-/
def StreamsNotified (work : Work) (initial : NodeRefs) (matching : PublicationMatching)
    (events : List WorkQueueEvent) (failed : FailureCuts)
    : Prop :=
  ∀ node dependencies producer,
    NodeAt work node .stream dependencies producer
    → (∀ source, producer = some source → Published matching events source)
    → ¬NodeFailed work matching events failed node.ref
    → node.ref ∈ announcedRefs initial events

/-- All enclosing defer refs of every stream have a completion in the supplied history.
This is a sufficient continuation boundary, not an invariant of arbitrary histories.
-/
def StreamDependenciesCompleted (work : Work) (events : List WorkQueueEvent) : Prop :=
  ∀ node dependencies producer,
    NodeAt work node .stream dependencies producer
    → ∀ ref ∈ dependencies, ref ∈ completedRefs events

/-- Appending observations preserves closed stream-dependency refs. Witness: membership
in the completed-ref list is monotone under history extension.
-/
theorem StreamDependenciesCompleted.append {work events}
    (closed : StreamDependenciesCompleted work events) (tail : List WorkQueueEvent)
    : StreamDependenciesCompleted work (events ++ tail) := by
  intro node dependencies producer known ref member
  simpa only [completedRefs, List.flatMap_append]
    using List.mem_append_left (completedRefs tail)
      (closed node dependencies producer known ref member)

/-- A healthy stream with closed dependencies has no remaining defer dependency.
Witness: if its dependency list is nonempty, at least one dependency is healthy, or the
all-dependencies-failed causal rule would fail the stream itself.
-/
theorem stream_dependencies_of_completed
    {work initial groups streams matching events failed node dependencies producer}
    (explained : Explains work groups streams events matching failed)
    (closed : StreamDependenciesCompleted work events)
    (known : NodeAt work node .stream dependencies producer)
    (healthy : ¬NodeFailed work matching events failed node.ref)
    : dependencies = []
      ∨ ∃ ref ∈ dependencies,
          DependencySatisfied work initial matching events failed ref := by
  classical
  by_cases empty : dependencies = []
  · exact Or.inl empty
  · have existsHealthy : ∃ ref ∈ dependencies, ¬NodeFailed work matching events failed ref := by
      apply Classical.byContradiction
      intro absent
      apply healthy
      apply explained.snapshot_nodeFailed
      apply Causality.NodeFailed.streamDependencies ⟨node, producer, known, rfl⟩ empty
      intro ref member
      exact explained.nodeFailed_snapshot
        (Classical.byContradiction (fun health => absent ⟨ref, member, health⟩))
    obtain ⟨ref, member, health⟩ := existsHealthy
    exact Or.inr ⟨ref, member, health,
      Or.inr (Or.inl (closed node dependencies producer known ref member))⟩

/-- A control event and additional failure evidence preserve stream notice coverage.
Witness: control events cannot publish a new producer, and failures cannot restore health.
-/
theorem StreamsNotified.append_control {work initial matching events failed more event}
    (notified : StreamsNotified work initial matching events failed)
    (control : ¬IsValue event) (included : failed ⊆ more)
    : StreamsNotified work initial matching (events ++ [event]) more := by
  intro node dependencies producer known ready healthy
  have earlier : ∀ source, producer = some source → Published matching events source := by
    intro source same
    rcases published_append_singleton_iff.mp (ready source same) with old | new
    · exact old
    · exact False.elim (control new.1)
  have member := notified node dependencies producer known earlier
    (fun failure => healthy ((failure.mono included).append [event]))
  simpa only [announcedRefs, pendingRefs, List.flatMap_append, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, List.append_assoc]
    using List.mem_append_left (eventPending event) member

-----------------------------------------------------------------------------------------
-- Both permitted carrier forms can install complete stream coverage
-----------------------------------------------------------------------------------------

/-- A covering frontier includes every ready healthy stream after its carrier.
Witness: replay the last-event publication independently of its notices, then use the
closed dependency refs in the eligibility prefix to license every fresh stream notice.
-/
private theorem streamsNotified_of_covering
    {work initial initialGroups initialStreams matching events failed plain actual}
    {groups streams : List DeliveryNode} (noNotices : eventPending plain = [])
    (notices : eventPending actual = (groups ++ streams).map DeliveryNode.ref)
    (sameValue : IsValue actual ↔ IsValue plain)
    (sameCompleted : eventCompleted actual = eventCompleted plain)
    (explained
      : Explains work initialGroups initialStreams (events ++ [actual]) matching failed)
    (closed : StreamDependenciesCompleted work (events ++ [plain]))
    (covers
      : ∀ node kind dependencies birth,
          NodeAt work node kind dependencies birth
          → CanAnnounce work initial matching (events ++ [plain]) failed
              node kind dependencies birth
          → node.ref ∈ (groups ++ streams).map DeliveryNode.ref)
    : StreamsNotified work initial matching (events ++ [actual]) failed := by
  classical
  have causal := causality_carrier_eq (work := work) (matching := matching)
    (events := events) (failures := failed) sameValue
  have closedActual : StreamDependenciesCompleted work (events ++ [actual]) := by
    intro node dependencies producer known ref member
    simpa only [completedRefs, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, sameCompleted]
      using closed node dependencies producer known ref member
  intro node dependencies producer known produced healthy
  by_cases old : node.ref ∈ announcedRefs initial events
  · simpa only [announcedRefs, pendingRefs, List.flatMap_append, List.flatMap_cons,
      List.flatMap_nil, List.append_nil, List.append_assoc]
      using List.mem_append_left (eventPending actual) old
  · have eligible : CanAnnounce work initial matching (events ++ [plain]) failed
        node .stream dependencies producer := by
      refine ⟨?_, Or.inl ⟨by simpa only [causal.1] using healthy, Or.inl rfl⟩, ?_, ?_⟩
      · simpa [announcedRefs, pendingRefs, noNotices] using old
      · intro source same
        rcases published_append_singleton_iff.mp (produced source same) with earlier | last
        · exact earlier.append [plain]
        · exact published_append_singleton_iff.mpr (Or.inr ⟨sameValue.mp last.1, last.2⟩)
      · rcases stream_dependencies_of_completed (initial := initial) explained
          closedActual known healthy with empty | ⟨ref, member, supported⟩
        · exact Or.inl empty
        · exact Or.inr ⟨ref, member, by simpa only [causal.1] using supported.1,
            Or.inr (Or.inl (closed node dependencies producer known ref member))⟩
    have added := covers node .stream dependencies producer known eligible
    simpa only [announcedRefs, pendingRefs, List.flatMap_append, List.flatMap_cons,
      List.flatMap_nil, List.append_nil, List.append_assoc, notices]
      using List.mem_append_right (announcedRefs initial events) added

/-- A ready item can publish and cover every newly produced stream once defer dependencies
have closed. Witness: the complete eligible frontier on its actual stream-value event.
-/
theorem Explains.publish_item_streams_notified
    {work groups streams events matching failures occurrence owners producer node item
      errors}
    (explained : Explains work groups streams events matching failures)
    (closed : StreamDependenciesCompleted work events)
    (known : TaskAt work occurrence owners producer (.item node (.ok (item, errors))))
    (ready : CanPublish work matching events failures occurrence producer)
    (selected
      : PublicationOwner work ((groups ++ streams).map DeliveryNode.ref) matching events
          failures owners node)
    : ∃ newGroups newStreams,
        Explains work groups streams
          (events ++ [.streamValues node [{ item, errors }] newGroups newStreams])
          (matchNext matching events.length occurrence) failures
        ∧ StreamsNotified work ((groups ++ streams).map DeliveryNode.ref)
            (matchNext matching events.length occurrence)
            (events ++ [.streamValues node [{ item, errors }] newGroups newStreams])
            failures := by
  obtain ⟨newGroups, newStreams, extended, covers⟩ :=
    explained.publish_item_covering known ready selected
  refine ⟨newGroups, newStreams, extended, ?_⟩
  exact streamsNotified_of_covering
    (plain := .streamValues node [{ item, errors }] [] [])
    rfl rfl Iff.rfl rfl extended (closed.append _) covers

/-- Closing an accounted healthy group can release and announce nested streams.
Witness: the group-success carrier's covering frontier, provided this closure leaves all
stream-dependency refs completed. Its nested stream tasks may still be wholly unprocessed.
-/
theorem Explains.complete_group_streams_notified
    {work groups streams events matching failures node dependencies birth}
    (explained : Explains work groups streams events matching failures)
    (known : NodeAt work node .group dependencies birth)
    (opened : Open ((groups ++ streams).map DeliveryNode.ref) events node.ref)
    (healthy : ¬NodeFailed work matching events failures node.ref)
    (accounted : NodeAccounted work matching events failures node.ref)
    (closed : StreamDependenciesCompleted work (events ++ [.groupSuccess node [] []]))
    : ∃ newGroups newStreams,
        Explains work groups streams (events ++ [.groupSuccess node newGroups newStreams])
          matching failures
        ∧ StreamsNotified work ((groups ++ streams).map DeliveryNode.ref) matching
            (events ++ [.groupSuccess node newGroups newStreams])
            failures := by
  obtain ⟨newGroups, newStreams, extended, covers⟩ :=
    explained.complete_group_covering known opened healthy accounted
  refine ⟨newGroups, newStreams, extended, ?_⟩
  exact streamsNotified_of_covering (plain := .groupSuccess node [] [])
    rfl rfl Iff.rfl rfl extended closed covers

end GraphQL.IncrementalDelivery.WorkQueueSemantics
