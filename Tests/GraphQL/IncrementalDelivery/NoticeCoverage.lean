import Proofs.GraphQL.IncrementalDelivery.WorkQueueSemantics.NoticeCoverage
import Proofs.GraphQL.IncrementalDelivery.WorkQueueSemantics.SingletonOwners
import Tests.GraphQL.IncrementalDelivery.HistoryScheduling

/-! Notice coverage after carriers, and the boundary between singleton and shared owners. -/

namespace GraphQL.IncrementalDelivery.Tests.NoticeCoverage
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Covering initialization leaves no eligible notice for the shared-work fixture.
Witness: complete-frontier construction and coverage after installing those notices.
-/
example (matching : PublicationMatching)
    : ∃ groups streams,
        Initializes HistoryScheduling.shared groups streams
        ∧ NoticesCovered HistoryScheduling.shared
            ((groups ++ streams).map DeliveryNode.key) matching [] [] := by
  obtain ⟨groups, streams, initialized, covers⟩ := HistoryScheduling.initialized.covering_exists
  exact ⟨groups, streams, initialized, NoticesCovered.initial covers matching⟩

/-- A published singleton root is not a satisfied dependency until its ID completes.
Witness: dependency reduction after the actual admitted object publication.
-/
example
    : ¬DependencySatisfied WorkQueueSemantics.work [0] WorkQueueSemantics.matching
        [WorkQueueSemantics.value] [] 0 := by
  have initial : Explains WorkQueueSemantics.work [WorkQueueSemantics.node] [] []
      WorkQueueSemantics.matching [] :=
    ⟨WorkQueueSemantics.initialized _, by simp [FailureWitness], by simp⟩
  have published := initial.append_event
    (by simpa [WorkQueueSemantics.node, failedBefore] using WorkQueueSemantics.publishes)
  have reduction := published.singleton_dependency_iff_completed
    (show TaskAt WorkQueueSemantics.work (.executionGroup []) [0] none (.object [] (.ok ([], 0)))
      from .executionGroup .root)
    (fun failure => failure.nonempty rfl)
  simpa [WorkQueueSemantics.node, WorkQueueSemantics.value, completedKeys, eventCompleted,
    failedBefore]
    using reduction

/-- Shared ownership really can account for an unannounced healthy key. Witness: announce
only the left owner and publish once; the right owner's dependency is satisfied without
a completion. This guards against applying singleton dependency reduction to shared work.
-/
example
    : ∃ events matching,
        Explains HistoryScheduling.shared [HistoryScheduling.left] [] events matching []
        ∧ DependencySatisfied HistoryScheduling.shared [0] matching events [] 1
        ∧ 1 ∉ announcedKeys [0] events
        ∧ 1 ∉ completedKeys events := by
  have task : TaskAt HistoryScheduling.shared (.executionGroup []) [0, 1] none
      (.object [] (.ok ([], 0))) := .executionGroup .root
  have initial : Explains HistoryScheduling.shared [HistoryScheduling.left] [] []
      HistoryScheduling.matching [] := by
    refine ⟨⟨⟨by simp, ?_, by simp⟩, by simp⟩, by simp [FailureWitness], by simp⟩
    intro node member
    have same := List.mem_singleton.mp member
    subst node
    exact HistoryScheduling.initialized.1.2.1 HistoryScheduling.left (by simp)
  have ready : CanPublish HistoryScheduling.shared HistoryScheduling.matching [] []
      (.executionGroup []) none :=
    ⟨by simp [Published], fun cancelled => cancelled.nonempty rfl, by simp, trivial⟩
  have owner : PublicationOwner HistoryScheduling.shared [0] HistoryScheduling.matching [] []
      [0, 1] HistoryScheduling.left := by
    have opened : OpenOwner HistoryScheduling.shared [0] [] [0, 1]
        HistoryScheduling.left :=
      ⟨⟨.group, [], none, .group (group := { node := HistoryScheduling.left })
        .root (by simp)⟩, by simp [HistoryScheduling.left],
        by simp [Open, announcedKeys, pendingKeys, completedKeys, HistoryScheduling.left]⟩
    refine ⟨opened, ⟨HistoryScheduling.left, opened, fun failure => failure.nonempty rfl⟩,
      ?_⟩
    intro other available
    obtain ⟨kind, parents, birth, known⟩ := available.1
    rcases (HistoryScheduling.node_shared known).1 with rfl | rfl <;>
      simp [HistoryScheduling.left, HistoryScheduling.right]
  have published := initial.publish_object task ready
    (by simpa [HistoryScheduling.left, failedBefore] using owner)
  let event := WorkQueueEvent.groupValues HistoryScheduling.left [{ path := [], data := [] }]
  let next := matchNext HistoryScheduling.matching 0 (.executionGroup [])
  refine ⟨[event], next, published, ⟨fun failure => failure.nonempty rfl,
    Or.inr (Or.inr ⟨?_, ?_⟩)⟩, ?_, ?_⟩
  · simp [announcedKeys, pendingKeys, event, eventPending]
  · rintro occurrence owners ⟨producer, payload, known⟩ _
    have same := HistoryScheduling.task_shared known
    subst occurrence
    exact Or.inr (published_matchNext (event := event) trivial
      HistoryScheduling.matching [] (.executionGroup []))
  · simp [announcedKeys, pendingKeys, event, eventPending]
  · simp [completedKeys, event, eventCompleted]

end GraphQL.IncrementalDelivery.Tests.NoticeCoverage
