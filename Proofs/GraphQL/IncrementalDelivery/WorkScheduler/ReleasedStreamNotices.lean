import Proofs.GraphQL.IncrementalDelivery.WorkScheduler.StreamNotices

/-! Notice carriers after deferred dependencies close. These are construction witnesses,
not additional premises on the public work-history relation.
-/

namespace GraphQL.IncrementalDelivery.WorkScheduler
open GraphQL.IncrementalDelivery.Execution

-----------------------------------------------------------------------------------------
-- Streams whose deferred dependencies have already closed
-----------------------------------------------------------------------------------------

/-- Every healthy stream with a published producer has already been announced.
Unlike parentless coverage, this witness also includes streams released by deferred work.
-/
def StreamsNotified (work : Work) (initial : Keys) (matching : PublicationMatching)
    (events : List WorkEvent) (failed : List Occurrence)
    : Prop :=
  ∀ node parents producer,
    NodeAt work node .stream parents producer
    → (∀ parent, producer = some parent → Published matching events parent)
    → ¬NodeFailed work failed node.key
    → node.key ∈ announcedKeys initial events

/-- All enclosing defer keys of every stream have a completion in the supplied history.
This is a sufficient continuation boundary, not an invariant of arbitrary histories.
-/
def StreamParentsCompleted (work : Work) (events : List WorkEvent) : Prop :=
  ∀ node parents producer,
    NodeAt work node .stream parents producer
    → ∀ key ∈ parents, key ∈ completedKeys events

/-- Appending observations preserves closed stream-parent keys. Witness: membership
in the completed-key list is monotone under history extension.
-/
theorem StreamParentsCompleted.append {work events}
    (closed : StreamParentsCompleted work events) (tail : List WorkEvent)
    : StreamParentsCompleted work (events ++ tail) := by
  intro node parents producer known key member
  simpa only [completedKeys, List.flatMap_append]
    using List.mem_append_left (completedKeys tail)
      (closed node parents producer known key member)

/-- A healthy stream with closed parents has no remaining defer dependency.
Witness: if its parent list is nonempty, at least one parent is healthy, or the causal
all-parents-failed rule would fail the stream itself.
-/
theorem stream_dependencies_of_completed
    {work initial matching events failed node parents producer}
    (closed : StreamParentsCompleted work events)
    (known : NodeAt work node .stream parents producer)
    (healthy : ¬NodeFailed work failed node.key)
    : parents = []
      ∨ ∃ key ∈ parents, DependencySatisfied work initial matching events failed key := by
  classical
  by_cases empty : parents = []
  · exact Or.inl empty
  · have existsHealthy : ∃ key ∈ parents, ¬NodeFailed work failed key := by
      apply Classical.byContradiction
      intro absent
      apply healthy
      apply NodeFailed.streamParents known empty
      intro key member
      exact Classical.byContradiction (fun health => absent ⟨key, member, health⟩)
    obtain ⟨key, member, health⟩ := existsHealthy
    exact Or.inr ⟨key, member, health,
      Or.inr (Or.inl (closed node parents producer known key member))⟩

/-- A control event and additional failure evidence preserve stream notice coverage.
Witness: control events cannot publish a new producer, and failures cannot restore health.
-/
theorem StreamsNotified.append_control {work initial matching events failed more event}
    (notified : StreamsNotified work initial matching events failed)
    (control : ¬IsValue event) (included : failed ⊆ more)
    : StreamsNotified work initial matching (events ++ [event]) more := by
  intro node parents producer known ready healthy
  have earlier : ∀ parent, producer = some parent → Published matching events parent := by
    intro parent same
    rcases published_append_singleton_iff.mp (ready parent same) with old | new
    · exact old
    · exact False.elim (control new.1)
  have member := notified node parents producer known earlier
    (fun failure => healthy (failure.mono included))
  simpa only [announcedKeys, pendingKeys, List.flatMap_append, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, List.append_assoc]
    using List.mem_append_left (eventPending event) member

-----------------------------------------------------------------------------------------
-- Both permitted carrier forms can install complete stream coverage
-----------------------------------------------------------------------------------------

/-- A covering frontier includes every ready healthy stream after its carrier.
Witness: replay the last-event publication independently of its notices, then use the
closed parent keys in the eligibility prefix to license every fresh stream notice.
-/
private theorem streamsNotified_of_covering
    {work initial matching events failed plain actual}
    {groups streams : List DeliveryNode} (noNotices : eventPending plain = [])
    (notices : eventPending actual = (groups ++ streams).map DeliveryNode.key)
    (sameValue : IsValue actual ↔ IsValue plain)
    (closed : StreamParentsCompleted work (events ++ [plain]))
    (covers
      : ∀ node kind parents birth,
          NodeAt work node kind parents birth
          → CanAnnounce work initial matching (events ++ [plain]) failed
              node kind parents birth
          → node.key ∈ (groups ++ streams).map DeliveryNode.key)
    : StreamsNotified work initial matching (events ++ [actual]) failed := by
  classical
  intro node parents producer known produced healthy
  by_cases old : node.key ∈ announcedKeys initial events
  · simpa only [announcedKeys, pendingKeys, List.flatMap_append, List.flatMap_cons,
      List.flatMap_nil, List.append_nil, List.append_assoc]
      using List.mem_append_left (eventPending actual) old
  · have eligible : CanAnnounce work initial matching (events ++ [plain]) failed
        node .stream parents producer := by
      refine ⟨?_, healthy, Or.inl rfl, ?_,
        stream_dependencies_of_completed closed known healthy⟩
      · simpa [announcedKeys, pendingKeys, noNotices] using old
      · intro parent same
        rcases published_append_singleton_iff.mp (produced parent same) with earlier | last
        · exact earlier.append [plain]
        · exact published_append_singleton_iff.mpr (Or.inr ⟨sameValue.mp last.1, last.2⟩)
    have added := covers node .stream parents producer known eligible
    simpa only [announcedKeys, pendingKeys, List.flatMap_append, List.flatMap_cons,
      List.flatMap_nil, List.append_nil, List.append_assoc, notices]
      using List.mem_append_right (announcedKeys initial events) added

/-- A ready item can publish and cover every newly produced stream once defer parents
have closed. Witness: the complete eligible frontier on its actual stream-value event.
-/
theorem Explains.publish_item_streams_notified
    {work groups streams events matching failures occurrence owners producer node item
      errors}
    (explained : Explains work groups streams events matching failures)
    (closed : StreamParentsCompleted work events)
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
        ∧ StreamsNotified work ((groups ++ streams).map DeliveryNode.key)
            (matchNext matching events.length occurrence)
            (events ++ [.streamValues node [{ item, errors }] newGroups newStreams])
            (failures.map Prod.snd) := by
  obtain ⟨newGroups, newStreams, extended, covers⟩ :=
    explained.publish_item_covering known ready selected
  refine ⟨newGroups, newStreams, extended, ?_⟩
  rw [← explained.2.1.failedBefore_eq (Nat.le_refl _)]
  exact streamsNotified_of_covering
    (plain := .streamValues node [{ item, errors }] [] [])
    rfl rfl Iff.rfl (closed.append _) covers

/-- Closing an accounted healthy group can release and announce nested streams.
Witness: the group-success carrier's covering frontier, provided this closure leaves all
stream-parent keys completed. Its nested stream tasks may still be wholly unprocessed.
-/
theorem Explains.complete_group_streams_notified
    {work groups streams events matching failures node parents birth}
    (explained : Explains work groups streams events matching failures)
    (known : NodeAt work node .group parents birth)
    (opened : Open ((groups ++ streams).map DeliveryNode.key) events node.key)
    (healthy : ¬NodeFailed work (failedBefore failures events.length) node.key)
    (accounted
      : NodeAccounted work matching events (failedBefore failures events.length) node.key)
    (closed : StreamParentsCompleted work (events ++ [.groupSuccess node [] []]))
    : ∃ newGroups newStreams,
        Explains work groups streams (events ++ [.groupSuccess node newGroups newStreams])
          matching failures
        ∧ StreamsNotified work ((groups ++ streams).map DeliveryNode.key) matching
            (events ++ [.groupSuccess node newGroups newStreams])
            (failures.map Prod.snd) := by
  obtain ⟨newGroups, newStreams, extended, covers⟩ :=
    explained.complete_group_covering known opened healthy accounted
  refine ⟨newGroups, newStreams, extended, ?_⟩
  rw [← explained.2.1.failedBefore_eq (Nat.le_refl _)]
  exact streamsNotified_of_covering (plain := .groupSuccess node [] [])
    rfl rfl Iff.rfl closed covers

end GraphQL.IncrementalDelivery.WorkScheduler
