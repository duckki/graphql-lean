import Proofs.GraphQL.IncrementalDelivery.WorkScheduler.Independence
import Proofs.GraphQL.IncrementalDelivery.Correctness.WorkMetadata
import Tests.GraphQL.IncrementalDelivery.HistoryScheduling
import Tests.GraphQL.IncrementalDelivery.DeferredPhase

/-! Commuting successful outputs is weaker than equality of their ordered wire images. -/

namespace GraphQL.IncrementalDelivery.Tests.Independence
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.WorkScheduler
open GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Semantics

-----------------------------------------------------------------------------------------
-- Different object occurrences may share their selected owner
-----------------------------------------------------------------------------------------

/-- Different payloads make the two publication orders observably distinct. -/
def leftData : List (Name × ResponseValue) := [("left", .scalar "a")]

/-- The other payload targets a separate field at the same object path. -/
def rightData : List (Name × ResponseValue) := [("right", .scalar "b")]

/-- A shared-owner pair retains a produced child stream for subsequent notice handling. -/
def work : Work := DeferredPhase.work (.ok (leftData, 0)) (.ok (rightData, 0))

/-- The two object events use the same selected owner but distinct task occurrences. -/
def value (data : List (Name × ResponseValue)) : WorkEvent :=
  .groupValues (DeferredPhase.node 0) [{path := [], data}]

/-- Both orders are explained and account for exactly the same tasks, even with a shared
owner and a child awaiting a notice. Witness: the local object-commutation theorem.
-/
example
    : ∃ forward backward,
        Explains work [DeferredPhase.node 0, DeferredPhase.node 1] []
          [value leftData, value rightData] forward []
        ∧ Explains work [DeferredPhase.node 0, DeferredPhase.node 1] []
            [value rightData, value leftData] backward []
        ∧ ∀ occurrence,
            Accounted work forward [value leftData, value rightData] [] occurrence
            ↔ Accounted work backward [value rightData, value leftData] []
                occurrence := by
  have coherent : MixedOwnerPaths.WorkAt (fun _ => []) 3 work := by
    simp [work, DeferredPhase.work, MixedOwnerPaths.WorkAt, OwnerPaths.MapAt,
      OwnerPaths.mapNodes, OwnerPaths.fragmentNodes, OwnerPaths.Assigned, Below,
      DeferredPhase.node]
  have selected (owners : Keys) (member : 0 ∈ owners)
      : Owner work [0, 1] [] [] owners (DeferredPhase.node 0) := by
    refine ⟨⟨⟨.group, [], none,
      .group (group := {node := DeferredPhase.node 0}) (.left .root) (by simp)⟩,
      member, ?_, WorkScheduler.noFailure _ _⟩, ?_⟩
    · simp [Open, announcedKeys, pendingKeys, completedKeys, DeferredPhase.node]
    · intro other available
      obtain ⟨kind, parents, birth, known⟩ := available.1
      have assigned := workAt_node coherent known
      simp [← assigned.2, DeferredPhase.node]
  have empty : Explains work [DeferredPhase.node 0, DeferredPhase.node 1] [] []
      WorkScheduler.matching [] :=
    ⟨DeferredPhase.initialized _ _, by simp [FailureWitness], by simp⟩
  have left : TaskAt work (.deferred [0]) [0] none (.object [] (.ok (leftData, 0))) :=
    .deferred (.left .root)
  have right : TaskAt work (.deferred [1]) [0, 1] none (.object [] (.ok (rightData, 0))) :=
    .deferred (.right .root)
  have ready (address : Address) : CanPublish work WorkScheduler.matching [] []
      (.deferred address) none :=
    ⟨by simp [Published], WorkScheduler.noCancellation _ _, by simp, trivial⟩
  simpa [value, failedBefore, DeferredPhase.node]
    using empty.objects_commute left right (ready [0]) (ready [1])
      (selected [0] (by simp)) (selected [0, 1] (by simp)) (by decide)

-----------------------------------------------------------------------------------------
-- Shared-owner closures commute, but their wire order remains visible
-----------------------------------------------------------------------------------------

/-- The shared publication admits both completion orders with identical closed-key sets.
Witness: append the explicit publication, then commute the two enabled group closures.
-/
example
    : Explains HistoryScheduling.shared [HistoryScheduling.left, HistoryScheduling.right]
        []
        [
          HistoryScheduling.value HistoryScheduling.left,
          .groupSuccess HistoryScheduling.left [] [],
          .groupSuccess HistoryScheduling.right [] []
        ]
        HistoryScheduling.matching []
      ∧ Explains HistoryScheduling.shared
          [HistoryScheduling.left, HistoryScheduling.right] []
          [
            HistoryScheduling.value HistoryScheduling.left,
            .groupSuccess HistoryScheduling.right [] [],
            .groupSuccess HistoryScheduling.left [] []
          ]
          HistoryScheduling.matching [] := by
  have published : Explains HistoryScheduling.shared
      [HistoryScheduling.left, HistoryScheduling.right] []
      [HistoryScheduling.value HistoryScheduling.left] HistoryScheduling.matching [] := by
    refine ⟨HistoryScheduling.initialized, by simp [FailureWitness], ?_⟩
    intro index event selected
    cases index with
    | zero =>
        have same : event = HistoryScheduling.value HistoryScheduling.left := by
          simpa using selected.symm
        subst event
        simpa [failedBefore, HistoryScheduling.left, HistoryScheduling.right]
          using HistoryScheduling.publishes HistoryScheduling.left (by simp)
    | succ index => simp at selected
  have left := HistoryScheduling.closes HistoryScheduling.left (by simp)
  have right := HistoryScheduling.closes HistoryScheduling.right (by simp)
  have both := published.group_closures_commute
    (by simpa [failedBefore, HistoryScheduling.left, HistoryScheduling.right] using left)
    (by simpa [failedBefore, HistoryScheduling.left, HistoryScheduling.right] using right)
    (by decide)
  exact ⟨both.1, both.2.1⟩

/-- Reversing these independent initial notices is also allowed. Witness: the same
descriptor eligibility proofs and the same distinct-key check in reversed order.
-/
example
    : Initializes HistoryScheduling.shared
        [HistoryScheduling.right, HistoryScheduling.left] [] := by
  refine ⟨⟨by decide, ?_, by simp⟩, by simp⟩
  intro node member
  exact HistoryScheduling.initialized.1.2.1 node (by simpa [or_comm] using member)

/-- Legal notice permutations change the ID attached to a later identical object patch.
Witness: execute the real ID allocator and entry constructor in each notice order.
-/
example
    : ((getIncrementalEntry (m := StateM IDState)
          HistoryScheduling.left {path := [], data := leftData} ensureID).run
        ((getPendingEntry (m := StateM IDState)
            [HistoryScheduling.left, HistoryScheduling.right] [] ensureID).run
          {}).2).1
      = .object "0" leftData 0 [] := by rfl

/-- In the reversed legal notice order, that same patch refers to ID one, not zero.
Witness: reduction of the real mapper helpers, without quotienting IDs or entry order.
-/
example
    : ((getIncrementalEntry (m := StateM IDState)
          HistoryScheduling.left {path := [], data := leftData} ensureID).run
        ((getPendingEntry (m := StateM IDState)
            [HistoryScheduling.right, HistoryScheduling.left] [] ensureID).run
          {}).2).1
      = .object "1" leftData 0 [] := by rfl

/-- Even notice-free closures retain their order within a coalesced response batch.
Witness: both notices are already allocated; only the completed-entry order changes.
-/
example
    : let state :=
        ((getPendingEntry (m := StateM IDState)
            [HistoryScheduling.left, HistoryScheduling.right] [] ensureID).run
          {}).2
      ((mapWorkEventBatch
          [
            .groupSuccess HistoryScheduling.left [] [],
            .groupSuccess HistoryScheduling.right [] []
          ]).run
          state).1.completed.map
          (·.id)
        = ["0", "1"]
      ∧ ((mapWorkEventBatch
            [
              .groupSuccess HistoryScheduling.right [] [],
              .groupSuccess HistoryScheduling.left [] []
            ]).run
          state).1.completed.map
          (·.id)
        = ["1", "0"] := by decide

end GraphQL.IncrementalDelivery.Tests.Independence
