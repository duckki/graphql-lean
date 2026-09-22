import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.NoticeItemBoundary
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RawNoticeHistoryCompletion

/-! Earlier group notices remain permanently registered at every later source boundary. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Arbitrary source replay retains unique live group keys.
Witness: the per-handler key invariant follows the actual queue fold, including ignored inputs.
-/
theorem State.GroupKeysUnique.replayGraphEvents {queue : State}
    (keys : queue.GroupKeysUnique) (events : List GraphEvent)
    : (queue.replayGraphEvents events).GroupKeysUnique := by
  induction events generalizing queue with
  | nil => exact keys
  | cons event rest ih => exact ih (keys.handleGraphEvent event)

/-- Every group notice in matching raw replay remains in its final permanent registry.
Witness: each actual handler registers its notices; later matching handlers retain those
registrations. The result does not require output freshness or an abstract explanation.
-/
theorem State.rawEventReplay_groupNoticesRegistered {queue : State} {work}
    (keys : queue.GroupKeysUnique) (live : queue.LiveGroupsRegistered)
    (tasks : queue.TaskGroupsRegistered) (events : List GraphEvent)
    (matching : ∀ event ∈ events, event.MatchesWork work)
    : ∀ output ∈ (queue.rawEventReplay events).2,
        output.GroupNoticesRegistered
          (queue.replayGraphEvents events).registeredGroups := by
  induction events generalizing queue with
  | nil => simp [State.rawEventReplay]
  | cons event rest ih =>
      have matched := matching event List.mem_cons_self
      have later : ∀ entry ∈ rest, entry.MatchesWork work :=
        fun _ member => matching _ (List.mem_cons_of_mem _ member)
      have registered := queue.handleGraphEvent_registration live tasks event matched
      have continuation := State.replayGraphEvents_registration registered.1 registered.2.1
        rest later
      intro output member
      rw [State.rawEventReplay_cons] at member
      rcases List.mem_append.mp member with first | following
      · exact (queue.handleGraphEvent_groupNoticesRegistered keys live tasks event matched
          output first).mono continuation.2.2
      · exact ih (keys.handleGraphEvent event) registered.1 registered.2.1 later output following

/-- Initial and earlier-source group announcements remain registered at the next handler.
Witness: initialization gives live registered roots, and matching replay preserves both
their registrations and the registrations attached to each actual carried notice.
-/
theorem createWorkQueue_rawEventReplay_announcedRegistered {work : Execution.Work}
    (events : List GraphEvent) (matching : ∀ event ∈ events, event.MatchesWork work)
    : let initial := State.initialize (Work.fromExecution work)
      ∀ key ∈
        initial.rootGroups
        ++ (initial.rawEventReplay events).2.flatMap rawGroupNoticeKeys,
        key ∈ (initial.replayGraphEvents events).registeredGroups := by
  intro initial key announced
  have registered := createWorkQueue_registration work
  rcases List.mem_append.mp announced with root | pending
  · obtain ⟨node, member, same⟩ := List.mem_map.mp (createWorkQueue_rootGroupsPresent _ key root)
    exact (initial.replayGraphEvents_registration registered.1 registered.2 events
      matching).2.2 (same ▸ registered.1 node member)
  · obtain ⟨event, emitted, notice⟩ := List.mem_flatMap.mp pending
    exact (initial.rawEventReplay_groupNoticesRegistered (createWorkQueue_groupKeysUnique _)
      registered.1 registered.2 events matching event emitted).key notice

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
