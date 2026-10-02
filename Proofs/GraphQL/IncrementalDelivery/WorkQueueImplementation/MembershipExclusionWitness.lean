import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.MembershipExclusionPersistence
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ReplayValueConservation
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ClosureWitness
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.FlattenedClosureLedger

/-! The common replay ledger permanently excludes published memberships. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Each exact handler slice names registered tasks and clears its new memberships
-----------------------------------------------------------------------------------------

/-- Every label consumed by the raw output is a permanently registered task occurrence.
Witness: split the publication prefix at each raw event's exact object count, then use
that block's subsequence certificate. Equal payload values do not identify occurrences.
-/
theorem BlocksFollowRegistrations.registered {tasks published events}
    (ordered : BlocksFollowRegistrations tasks published events) {publication}
    (member
      : publication ∈ published.take (events.flatMap WorkQueueEvent.objectValues).length)
    : publication.1 ∈ tasks.map Task.occurrence := by
  induction events generalizing published with
  | nil => simp at member
  | cons event rest ih =>
      simp only [List.flatMap_cons, List.length_append, List.take_add] at member
      rcases List.mem_append.mp member with head | tail
      · exact ordered.1.subset (List.mem_map.mpr ⟨publication, head, rfl⟩)
      · exact ih ordered.2 tail

/-- Every object occurrence emitted by a handler has no live membership at its endpoint.
Witness: the full-budget internal drain certificate includes all owner-fold publications;
item handlers add no object offset before draining. Ignored inputs and other event kinds
emit no object values, so their exact consumed label prefix is empty.
-/
theorem State.PreparedMembershipsCleared.handler_membershipAbsent
    {queue : State} {event published publication}
    (cleared : queue.PreparedMembershipsCleared event published)
    (member
      : publication
        ∈ published.take
            ((queue.handleGraphEvent event).2.flatMap WorkQueueEvent.objectValues).length)
    : (queue.handleGraphEvent event).1.TaskMembershipAbsent publication.1 := by
  cases event with
  | taskSuccess occurrence result =>
      cases found : queue.taskNode? occurrence with
      | none => simp [State.handleGraphEvent, State.taskSuccess, found] at member
      | some node =>
          cases healthy : queue.taskHasHealthyOwner node.task with
          | false =>
              simp [State.handleGraphEvent, State.taskSuccess, found, healthy] at member
          | true =>
              have ready := cleared node found healthy
              let stored := queue.putTaskNode { node with value := some result.value }
              let prepared := (stored.maybeIntegrateWork result.work (some occurrence)).1
              let released := node.task.groups.foldl successGroupStep (prepared, [], {})
              let active := released.1.startNewWork released.2.2
              have final := ready.drain active.groupNodes.length (Nat.le_refl _) publication
              rw [State.handleGraphEvent, queue.taskSuccess_eq occurrence result node found]
              simp only [healthy, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
              apply final
              simpa only [State.handleGraphEvent, queue.taskSuccess_eq occurrence result node found,
                healthy, Bool.not_true, Bool.false_eq_true, ↓reduceIte, State.drainReadyGroups,
                active, released, prepared, stored] using member
  | streamItems stream items =>
      cases active : queue.rootStreams.contains stream.key with
      | false =>
          simp only [State.handleGraphEvent, State.streamItems_eq, active, Bool.not_false,
            ↓reduceIte, List.flatMap_nil, List.length_nil, List.take_zero,
            List.not_mem_nil] at member
      | true =>
          have final := cleared active (queue.preparedStreamItems items).groupNodes.length
            (Nat.le_refl _) publication
          rw [State.handleGraphEvent, queue.streamItems_eq stream items]
          simp only [active, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          apply final
          simpa only [State.handleGraphEvent, State.streamItems_eq, active, Bool.not_true,
            Bool.false_eq_true, ↓reduceIte, List.flatMap_cons, WorkQueueEvent.objectValues,
            List.nil_append, State.preparedStreamItems, State.drainReadyGroups] using member
  | taskFailure occurrence errors =>
      simp only [State.handleGraphEvent, State.taskFailure_objectValues, List.length_nil,
        List.take_zero, List.not_mem_nil] at member
  | streamSuccess stream =>
      simp only [State.handleGraphEvent, State.streamSuccess] at member
      split at member <;> simp [WorkQueueEvent.objectValues] at member
  | streamFailure stream errors =>
      simp only [State.handleGraphEvent, State.streamFailure] at member
      split at member <;> simp [WorkQueueEvent.objectValues] at member

-----------------------------------------------------------------------------------------
-- Later source handlers cannot restore any earlier occurrence on this same witness
-----------------------------------------------------------------------------------------

/-- Every consumed label on the supplied replay ledger is permanently registered.
Witness: each handler's block certificate registers its own slice, and subsequent handlers
only extend the permanent registry. No source-validity premise or new ledger is needed.
-/
theorem State.ReplayClosuresCovered.registered {queue : State} {events published}
    (covered : queue.ReplayClosuresCovered events published)
    : ∀ publication ∈
        published.take
          ((queue.rawEventReplay events).2.flatMap WorkQueueEvent.objectValues).length,
        publication.1 ∈ (queue.replayGraphEvents events).tasks.map Task.occurrence := by
  induction events generalizing queue published with
  | nil => simp [State.rawEventReplay]
  | cons event rest ih =>
      intro publication member
      simp only [State.rawEventReplay_cons, List.flatMap_append, List.length_append,
        List.take_add] at member
      rcases List.mem_append.mp member with head | tail
      · have registered :=
          covered.2.2.2.2.2.2.2.2.1.registered
            (by simpa only [List.take_take, Nat.min_self] using head)
        obtain ⟨task, member, same⟩ := List.mem_map.mp registered
        exact List.mem_map.mpr
          ⟨
            task,
            (queue.handleGraphEvent event).1.replayGraphEvents_tasks_subset rest member,
            same
          ⟩
      · exact ih covered.tail publication tail

/-- Every consumed occurrence on a supplied common ledger is absent after replay.
Witness: a handler's drain certificate clears its exact label slice; its block-order
certificate registers those same occurrences. Source-ready registration then preserves
their exclusion through all remaining inputs. No replacement ledger is chosen.
-/
theorem State.ReplayClosuresCovered.membershipsAbsent {queue : State}
    {work before events published}
    (covered : queue.ReplayClosuresCovered events published)
    (ready : TaskProducersSucceeded work queue.tasks before)
    (ordered : ProducerOrder work (queue.tasks.map Task.occurrence))
    (valid : ValidGraphEvents work (before ++ events))
    : ∀ publication ∈
        published.take
          ((queue.rawEventReplay events).2.flatMap WorkQueueEvent.objectValues).length,
        (queue.replayGraphEvents events).TaskMembershipAbsent publication.1 := by
  induction events generalizing queue before published with
  | nil => simp [State.rawEventReplay]
  | cons event rest ih =>
      have earlier : (before ++ [event]).IsPrefix (before ++ event :: rest) := ⟨rest, by simp⟩
      obtain ⟨matching, fresh, _⟩ := valid.atPrefix earlier
      have next := State.handleGraphEvent_producerOrder ready ordered
        (valid.prefix (List.prefix_append before (event :: rest))) matching fresh
      have laterValid : ValidGraphEvents work ((before ++ [event]) ++ rest) := by
        simpa only [List.append_assoc, List.singleton_append] using valid
      intro publication member
      simp only [State.rawEventReplay_cons, List.flatMap_append, List.length_append,
        List.take_add] at member
      rcases List.mem_append.mp member with head | tail
      · have inSlice : publication ∈ (published.take
            ((queue.handleGraphEvent event).2.flatMap WorkQueueEvent.objectValues).length).take
              ((queue.handleGraphEvent event).2.flatMap WorkQueueEvent.objectValues).length := by
          simpa only [List.take_take, Nat.min_self] using head
        have removed := covered.2.2.2.2.2.2.2.1.handler_membershipAbsent inSlice
        have registered := covered.2.2.2.2.2.2.2.2.1.registered inSlice
        exact removed.replayGraphEvents_registered registered next.1 next.2 rest
          laterValid
      · exact ih covered.tail next.1 next.2 laterValid publication tail

/-- The chosen replay ledger excludes published memberships at every source prefix.
Witness: truncate only the source certificate, not its occurrence labels; initialization
supplies producer-ready registration, and the prefix theorem uses source validity alone.
-/
theorem createWorkQueue_replay_membershipsAbsent {work events published}
    (covered
      : (State.initialize (Work.fromExecution work)).ReplayClosuresCovered events
          published)
    (valid : ValidGraphEvents work events) {before : List GraphEvent}
    (earlier : before.IsPrefix events)
    : ∀ publication ∈
        published.take
          (((State.initialize (Work.fromExecution work)).rawEventReplay before).2.flatMap
            WorkQueueEvent.objectValues).length,
        ((State.initialize (Work.fromExecution work)).replayGraphEvents
          before).TaskMembershipAbsent
          publication.1 := by
  obtain ⟨after, same⟩ := earlier
  have restricted := State.ReplayClosuresCovered.prefix before after (same.symm ▸ covered)
  exact restricted.membershipsAbsent (createWorkQueue_producerOrder work).1
    (createWorkQueue_producerOrder work).2 (valid.prefix ⟨after, same⟩)

namespace ConformancePlan

/-- The canonical conformance ledger excludes published memberships at all source boundaries.
Witness: flatten started batches without changing their labels, then use the pointwise
replay theorem. The retained `ObjectLedgerMatching` relates exactly this ledger to `w`;
no payload-equality argument or independently chosen matching is used.
-/
theorem BufferedClosureLedger.membershipsAbsent {work inputs w}
    (ledger : BufferedClosureLedger work inputs w)
    (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    : ∃ published : List ObjectPublication,
        ObjectLedgerMatching work inputs w.events w.matching published
        ∧ ∀ before,
            before.IsPrefix inputs.flatten
            → ∀ publication ∈
                published.take
                  (((initialQueue work).rawEventReplay before).2.flatMap
                    WorkQueueEvent.objectValues).length,
                ((initialQueue work).replayGraphEvents before).TaskMembershipAbsent
                  publication.1 := by
  obtain ⟨published, batches, matching, _⟩ := ledger
  refine ⟨published, matching, ?_⟩
  intro before earlier
  exact createWorkQueue_replay_membershipsAbsent
    (batches.flatten (by rwa [← inputsStarted_eq_batchesStarted])) valid earlier

end ConformancePlan
end GraphQL.IncrementalDelivery.ReferenceWorkQueue
