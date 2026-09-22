import Proofs.GraphQL.IncrementalDelivery.WorkScheduler.Minimality
import Proofs.GraphQL.IncrementalDelivery.WorkScheduler.Independence
import Tests.GraphQL.IncrementalDelivery.HistoryScheduling
import Tests.GraphQL.IncrementalDelivery.FailureReporting

/-! Clause-removal witnesses and the nonempty-ownership boundary of terminal redundancy. -/

namespace GraphQL.IncrementalDelivery.Tests.Minimality
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.WorkScheduler

-----------------------------------------------------------------------------------------
-- Failure uniqueness is derived, not an admission premise
-----------------------------------------------------------------------------------------

/-- The shortened witness implies the old explicit uniqueness clause for arbitrary work.
Witness: the general licensing-derived uniqueness theorem, with no ownership premise.
-/
example {work initial events failures}
    (witness : FailureWitness work initial events failures)
    : (failures.map Prod.snd).Nodup :=
  witness.nodup

/-- Duplicated actual failures are still rejected after removing the explicit clause.
Witness: derived occurrence uniqueness, even when both cuts name a genuinely failing task.
-/
example (events : List WorkEvent)
    : ¬FailureWitness WorkScheduler.failingWork [0] events
        [(0, .executionGroup []), (0, .executionGroup [])] := by
  intro witness
  have unique := witness.nodup
  simp at unique

-----------------------------------------------------------------------------------------
-- Readiness, failure licensing, and counted errors are not interchangeable
-----------------------------------------------------------------------------------------

/-- Dropping freshness permits another owner to repeat the same object publication.
Witness: provenance, cancellation, producer, item, and owner clauses all still hold.
-/
example
    : let events := [HistoryScheduling.value HistoryScheduling.left]
      TaskAt HistoryScheduling.shared (.executionGroup []) [0, 1] none
        (.object [] (.ok ([], 0)))
      ∧ ¬TaskCancelled HistoryScheduling.shared [] (.executionGroup [])
      ∧ (∀ parent,
          (none : Option Occurrence) = some parent
          → Published HistoryScheduling.matching events parent)
      ∧ Owner HistoryScheduling.shared [0, 1] events [] [0, 1] HistoryScheduling.right
      ∧ ¬CanPublish HistoryScheduling.shared HistoryScheduling.matching events []
          (.executionGroup []) none := by
  refine ⟨.executionGroup .root, WorkScheduler.noCancellation _ _, by simp, ?_, ?_⟩
  · exact owner_after_object.mpr (HistoryScheduling.owner _ (by simp))
  · intro ready
    exact ready.1 ⟨0, _, rfl, trivial, rfl⟩

/-- Dropping previous-item publication releases the second stream position immediately.
Witness: every other CanPublish clause holds, but no first-item publication exists.
-/
example
    : ¬Published HistoryScheduling.itemMatching [] (.item [] 1)
      ∧ ¬TaskCancelled HistoryScheduling.items [] (.item [] 1)
      ∧ (∀ parent,
          (none : Option Occurrence) = some parent
          → Published HistoryScheduling.itemMatching [] parent)
      ∧ ¬CanPublish HistoryScheduling.items HistoryScheduling.itemMatching [] []
          (.item [] 1) none := by
  refine ⟨by simp [Published], WorkScheduler.noCancellation _ _, by simp, ?_⟩
  rintro ⟨_, _, _, previous⟩
  simp [Published] at previous

/-- An unlicensed failure could cancel an unannounced task without any output.
Witness: the causal kernel accepts a recorded failure, whereas ordered failure licensing
rejects its missing open owner. The kernel alone is not an admission contract.
-/
example
    : TaskCancelled FailureReporting.wk [FailureReporting.badID] FailureReporting.badID
      ∧ ¬FailureWitness FailureReporting.wk [0] [] [(0, FailureReporting.badID)] := by
  refine ⟨TaskCancelled.of_recorded FailureReporting.badTask (by simp) (by simp), ?_⟩
  intro witness
  obtain ⟨key, member, opened⟩ := witness.open_owner (cut := 0) (by simp)
    FailureReporting.badTask
  have same : key = 1 := by simpa using member
  subst key
  simpa [Open, announcedKeys, pendingKeys] using opened.1

/-- Known failure and an open owner alone do not enforce the reported error count.
Witness: the two-error task contributes at least two, so zero cannot satisfy NodeErrors.
-/
example
    : NodeFailed WorkScheduler.failingWork [.executionGroup []] 0
      ∧ Open [0] [] 0
      ∧ ¬NodeErrors WorkScheduler.failingWork [.executionGroup []] 0 0 := by
  have known : TaskAt WorkScheduler.failingWork (.executionGroup []) [0] none
      (.object [] (.error 2)) := .executionGroup .root
  refine ⟨NodeFailed.task known (by simp) (by simp), ?_, ?_⟩
  · simp [Open, announcedKeys, pendingKeys, completedKeys]
  · intro counted
    have bound := counted.contribution_le (by simp) known (by simp)
    simp [Payload.failure] at bound

-----------------------------------------------------------------------------------------
-- Raw ownerless work keeps the terminal task clause meaningful
-----------------------------------------------------------------------------------------

/-- One empty stream supplies legal notices alongside a task with no owning node. -/
def orphanWork : Work :=
  .combine (.stream WorkScheduler.node []) (.executionGroup [] [] (.ok ([], 0)) .empty)

/-- Only the root append, its two children, and the empty deferred child are located.
Witness: structural navigation; subtree shape suffices for this boundary example.
-/
private theorem orphan_locations {address current producer owners}
    (known : Located orphanWork address current producer owners)
    : current = orphanWork
      ∨ current = .stream WorkScheduler.node []
      ∨ current = .executionGroup [] [] (.ok ([], 0)) .empty
      ∨ current = .empty := by
  replace known := StructuralEquivalence.located_of_current known
  induction known with
  | root => exact Or.inl rfl
  | left _ ih | right _ ih | executionGroup _ ih | item _ _ ih =>
      rcases ih with h | h | h | h <;> simp_all [orphanWork]

/-- The ownerless task introduces no node descriptor. Witness: invert node lookup.
-/
private theorem orphan_node {node kind parents birth}
    (known : NodeAt orphanWork node kind parents birth)
    : node = WorkScheduler.node ∧ kind = .stream := by
  cases kind with
  | group =>
      obtain ⟨address, groups, path, result, children, enclosing, group,
        located, member, _, _⟩ := known
      rcases orphan_locations located with h | h | h | h <;> simp_all [orphanWork]
  | stream =>
      obtain ⟨address, items, located⟩ := known
      rcases orphan_locations located with h | h | h | h <;> simp_all [orphanWork]

/-- No task contributes to the empty stream. Witness: task lookup has only empty owners.
-/
private theorem orphan_accounted
    : NodeAccounted orphanWork WorkScheduler.matching [] [] 0 := by
  rintro occurrence owners ⟨producer, payload, known⟩ member
  cases occurrence with
  | executionGroup address =>
      obtain ⟨groups, path, result, children, enclosing, located, _, _⟩ := known
      rcases orphan_locations located with h | h | h | h <;> simp_all [orphanWork]
  | item address index =>
      obtain ⟨node, items, enclosing, result, children, located, entry, _, _⟩ := known
      rcases orphan_locations located with h | h | h | h <;> simp_all [orphanWork]

/-- Even an explained history can close every node while leaving raw ownerless work.
Witness: close the empty stream; the successful ownerless task remains unpublished and
uncancelled. Generated nonempty ownership is essential to the redundancy theorem.
-/
example
    : ∃ events,
        Explains orphanWork [] [WorkScheduler.node] events WorkScheduler.matching []
        ∧ NodesTerminal orphanWork [0] WorkScheduler.matching events []
        ∧ ¬Terminal orphanWork [0] WorkScheduler.matching events [] := by
  have initial : Initializes orphanWork [] [WorkScheduler.node] := by
    refine ⟨⟨by simp, by simp, ?_⟩, by simp⟩
    intro node member
    obtain rfl := List.mem_singleton.mp member
    refine ⟨[], none, .stream (.left .root), ?_⟩
    exact ⟨by simp [announcedKeys, pendingKeys], WorkScheduler.noFailure _ _,
      Or.inl rfl, by simp, Or.inl rfl⟩
  have empty : Explains orphanWork [] [WorkScheduler.node] [] WorkScheduler.matching [] :=
    ⟨initial, by simp [FailureWitness], by simp⟩
  have allowed : EventAllowed orphanWork [0] WorkScheduler.matching [] []
      (.streamSuccess WorkScheduler.node) := by
    exact ⟨⟨[], none, .stream (.left .root)⟩,
      by simp [Open, announcedKeys, pendingKeys, completedKeys, WorkScheduler.node],
      WorkScheduler.noFailure _ _, orphan_accounted⟩
  refine ⟨[.streamSuccess WorkScheduler.node], ?_, ?_, ?_⟩
  · simpa [WorkScheduler.node, failedBefore] using empty.append_event allowed
  · intro node kind parents birth known
    obtain ⟨rfl, _⟩ := orphan_node known
    exact Or.inl (by simp [completedKeys, eventCompleted])
  · intro terminal
    have known : TaskAt orphanWork (.executionGroup [1]) [] none (.object [] (.ok ([], 0))) :=
      .executionGroup (.right .root)
    rcases terminal.1 _ _ _ _ known with cancelled | published
    · exact WorkScheduler.noCancellation _ _ cancelled
    · rcases published with ⟨index, event, selected, value, _⟩
      cases index with
      | zero =>
          have same : event = .streamSuccess WorkScheduler.node := by
            simpa using selected.symm
          subst event
          exact value
      | succ index => simp at selected

end GraphQL.IncrementalDelivery.Tests.Minimality
