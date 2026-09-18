import Proofs.GraphQL.IncrementalDelivery.WorkScheduler.NoticeFrontiers
import Tests.GraphQL.IncrementalDelivery.HistoryScheduling

/-! Complete eligible notice frontiers, including notices introduced by item publication. -/

namespace GraphQL.IncrementalDelivery.Tests.NoticeFrontiers
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.WorkScheduler

/-- Completing an initial frontier retains both independent shared-work owner keys.
Witness: both original notices are eligible, so the covering frontier contains each key.
-/
example
    : ∃ groups streams,
        Initializes HistoryScheduling.shared groups streams
        ∧ 0 ∈ (groups ++ streams).map DeliveryNode.key
        ∧ 1 ∈ (groups ++ streams).map DeliveryNode.key := by
  obtain ⟨groups, streams, initialized, covers⟩ :=
    HistoryScheduling.initialized.covering_exists
  have left := HistoryScheduling.initialized.1.2.1 HistoryScheduling.left (by simp)
  have right := HistoryScheduling.initialized.1.2.1 HistoryScheduling.right (by simp)
  obtain ⟨leftParents, leftBirth, leftKnown, leftEligible⟩ := left
  obtain ⟨rightParents, rightBirth, rightKnown, rightEligible⟩ := right
  exact ⟨groups, streams, initialized,
    covers _ .group _ _ leftKnown leftEligible,
    covers _ .group _ _ rightKnown rightEligible⟩

/-- A stream item may create a fresh stream boundary in its child work. -/
def nested : Work :=
  .stream HistoryScheduling.left
    [(.ok (.null, 0), .stream HistoryScheduling.right [(.ok (.null, 0), .empty)])]

/-- Publishing the parent item makes its child stream eligible in the same carrier.
Witness: the exact producer publication and reset enclosing-owner context.
-/
theorem child_eligible
    : CanAnnounce nested [0] (fun _ => .item [] 0)
        [.streamValues HistoryScheduling.left [{ item := .null }] [] []] []
        HistoryScheduling.right .stream [] (some (.item [] 0)) := by
  refine ⟨
    by simp [announcedKeys, pendingKeys, eventPending, HistoryScheduling.right],
    fun failure => failure.nonempty rfl,
    Or.inl rfl,
    ?_,
    Or.inl rfl
  ⟩
  intro producer same
  have equal := Option.some.inj same
  subst producer
  exact ⟨0, _, rfl, trivial, rfl⟩

/-- The covering frontier includes that freshly eligible child key without a manually
supplied notice list. Witness: generic frontier construction over existing work nodes.
-/
example
    : ∃ groups streams,
        Announcements nested [0] (fun _ => .item [] 0)
          [.streamValues HistoryScheduling.left [{ item := .null }] [] []] [] groups
          streams
        ∧ 1 ∈ (groups ++ streams).map DeliveryNode.key := by
  obtain ⟨groups, streams, announced, covers⟩ := announcements_covering_exists nested [0]
    (fun _ => .item [] 0) [.streamValues HistoryScheduling.left [{ item := .null }] [] []] []
  exact ⟨groups, streams, announced,
    covers HistoryScheduling.right .stream [] (some (.item [] 0))
      (.stream (.item .root rfl)) child_eligible⟩

/-- Empty work has an empty covering frontier; nonemptiness is an initialization issue,
not a requirement invented for every later notice-bearing event.
-/
example : Announcements .empty [] (fun _ => .deferred []) [] [] [] [] := by
  simp [Announcements]

end GraphQL.IncrementalDelivery.Tests.NoticeFrontiers
