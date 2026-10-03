import Proofs.GraphQL.IncrementalDelivery.WorkQueueSemantics.Minimality
import Proofs.GraphQL.IncrementalDelivery.WorkQueueSemantics.Independence
import Tests.GraphQL.IncrementalDelivery.HistoryScheduling
import Tests.GraphQL.IncrementalDelivery.FailureReporting

/-! Clause-removal witnesses and the nonempty-ownership boundary of terminal redundancy. -/

namespace GraphQL.IncrementalDelivery.Tests.Minimality
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Failure uniqueness is derived, not an admission premise
-----------------------------------------------------------------------------------------

/-- Failure uniqueness is derived for arbitrary admitted work, not assumed.
Witness: provenance excludes failed publications, and failure licensing excludes repeats.
-/
example {work groups streams events matching failures}
    (explained : Explains work groups streams events matching failures)
    : (failures.map Prod.snd).Nodup :=
  explained.failures_nodup

/-- Duplicated actual failures at the initial cut are rejected even before event checking.
Witness: the first failure cancels the unpublished task in the empty cut snapshot.
-/
example (events : List WorkQueueEvent)
    : ¬FailureWitness WorkQueueSemantics.failingWork [0] WorkQueueSemantics.matching
        events [(0, .executionGroup []), (0, .executionGroup [])] := by
  intro witness
  have uncancelled :=
    (witness [(0, .executionGroup [])] 0 (.executionGroup []) [] rfl).2.2.2
  exact uncancelled WorkQueueSemantics.cancelled

/-- Licensing alone does not exclude a forged successful publication of a failing task.
Witness: both duplicate failures occur after that forged publication, which blocks the
kernel's self-cancellation. Full event provenance rejects this fixture below.
-/
theorem forgedPublication_failureWitness
    : FailureWitness WorkQueueSemantics.failingWork [0] WorkQueueSemantics.matching
        [WorkQueueSemantics.value]
        [(1, .executionGroup []), (1, .executionGroup [])] := by
  have known : TaskAt WorkQueueSemantics.failingWork (.executionGroup []) [0] none
      (.object [] (.error 2)) := .executionGroup .root
  have licensed : ∃ owners producer payload,
      TaskAt WorkQueueSemantics.failingWork (.executionGroup []) owners producer payload
      ∧ payload.failure.isSome = true
      ∧ Reachable WorkQueueSemantics.failingWork (.executionGroup [])
      ∧ ∃ ref ∈ owners, ref ∈ announcedRefs [0] [WorkQueueSemantics.value] :=
    ⟨[0], none, .object [] (.error 2), known, rfl, .root ⟨_, _, known⟩, 0, by simp,
      by simp [announcedRefs, pendingRefs, eventPending, WorkQueueSemantics.value]⟩
  have uncancelled : ¬TaskCancelled WorkQueueSemantics.failingWork WorkQueueSemantics.matching
      [WorkQueueSemantics.value] [(1, .executionGroup [])] (.executionGroup []) := by
    rintro ⟨cut, member, _, cause⟩
    have same : cut = 1 := by simpa using member
    subst cut
    exact cause.unpublished ⟨0, WorkQueueSemantics.value, rfl, trivial, rfl⟩
  intro before cut occurrence after equal
  cases before with
  | nil =>
      have same : cut = 1 ∧ occurrence = .executionGroup []
          ∧ after = [(1, .executionGroup [])] := by
        simpa [Prod.mk.injEq, and_assoc] using equal.symm
      rcases same with ⟨rfl, rfl, rfl⟩
      exact ⟨by simp, by simp, licensed, WorkQueueSemantics.noCancellation _ _⟩
  | cons first rest =>
      cases rest with
      | nil =>
          have firstEq := (List.cons.inj equal).1
          have same : cut = 1 ∧ occurrence = .executionGroup [] ∧ after = [] := by
            simpa [Prod.mk.injEq, and_assoc] using (List.cons.inj equal).2.symm
          rcases same with ⟨rfl, rfl, rfl⟩
          subst first
          exact ⟨by simp, by simp, licensed, uncancelled⟩
      | cons second rest =>
          have impossible := congrArg List.length equal
          simp at impossible

/-- The forged fixture cannot be an admitted history.
Witness: explained histories have unique failure occurrences; the supplied list repeats.
-/
example
    : ¬Explains WorkQueueSemantics.failingWork [WorkQueueSemantics.node] []
        [WorkQueueSemantics.value] WorkQueueSemantics.matching
        [(1, .executionGroup []), (1, .executionGroup [])] := by
  intro explained
  have unique := explained.failures_nodup
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
      ∧ ¬TaskCancelled HistoryScheduling.shared HistoryScheduling.matching events []
          (.executionGroup [])
      ∧ (∀ parent,
          (none : Option Occurrence) = some parent
          → Published HistoryScheduling.matching events parent)
      ∧ PublicationOwner HistoryScheduling.shared [0, 1] HistoryScheduling.matching events
          [] [0, 1] HistoryScheduling.right
      ∧ ¬CanPublish HistoryScheduling.shared HistoryScheduling.matching events []
          (.executionGroup []) none := by
  refine ⟨.executionGroup .root, WorkQueueSemantics.noCancellation _ _, by simp, ?_, ?_⟩
  · exact (owner_after_object (by simp)).mpr (HistoryScheduling.owner _ (by simp))
  · intro ready
    exact ready.1 ⟨0, _, rfl, trivial, rfl⟩

/-- Dropping previous-item publication releases the second stream position immediately.
Witness: every other CanPublish clause holds, but no first-item publication exists.
-/
example
    : ¬Published HistoryScheduling.itemMatching [] (.item [] 1)
      ∧ ¬TaskCancelled HistoryScheduling.items HistoryScheduling.itemMatching [] []
          (.item [] 1)
      ∧ (∀ parent,
          (none : Option Occurrence) = some parent
          → Published HistoryScheduling.itemMatching [] parent)
      ∧ ¬CanPublish HistoryScheduling.items HistoryScheduling.itemMatching [] []
          (.item [] 1) none := by
  refine ⟨by simp [Published], WorkQueueSemantics.noCancellation _ _, by simp, ?_⟩
  rintro ⟨_, _, _, previous⟩
  simp [Published] at previous

/-- An unlicensed failure could cancel an unannounced task without any output.
Witness: the causal kernel accepts a recorded failure, whereas ordered failure licensing
rejects its missing announced owner. The kernel alone is not an admission contract.
-/
example
    : TaskCancelled FailureReporting.wk WorkQueueSemantics.matching []
        [(0, FailureReporting.badID)] FailureReporting.badID
      ∧ ¬FailureWitness FailureReporting.wk [0] WorkQueueSemantics.matching []
          [(0, FailureReporting.badID)] := by
  refine ⟨
    TaskCancelled.of_recorded FailureReporting.badTask (by simp)
      (by simp [Published]) (by simp [failedBefore]),
    ?_
  ⟩
  intro witness
  obtain ⟨ref, member, announced⟩ := witness.announced_owner (cut := 0) (by simp)
    FailureReporting.badTask
  have same : ref = 1 := by simpa using member
  subst ref
  simp [announcedRefs, pendingRefs] at announced

/-- Known failure and an open owner alone do not enforce the reported error count.
Witness: the two-error task contributes at least two, so zero cannot satisfy NodeErrors.
-/
example
    : NodeFailed WorkQueueSemantics.failingWork WorkQueueSemantics.matching []
        [(0, .executionGroup [])] 0
      ∧ Open [0] [] 0
      ∧ ¬NodeErrors WorkQueueSemantics.failingWork [.executionGroup []] 0 0 := by
  have known : TaskAt WorkQueueSemantics.failingWork (.executionGroup []) [0] none
      (.object [] (.error 2)) := .executionGroup .root
  refine ⟨NodeFailed.task known (by simp) (by simp [failedBefore]), ?_, ?_⟩
  · simp [Open, announcedRefs, pendingRefs, completedRefs]
  · intro counted
    have bound := counted.contribution_le (by simp) known (by simp)
    simp [Payload.failure] at bound

-----------------------------------------------------------------------------------------
-- Raw ownerless work keeps the terminal task clause meaningful
-----------------------------------------------------------------------------------------

/-- One empty stream supplies legal notices alongside a task with no owning node. -/
def orphanWork : Work :=
  .combine (.stream WorkQueueSemantics.node [])
    (.executionGroup [] [] (.ok ([], 0)) .empty)

/-- Only the root append, its two children, and the empty deferred child are located.
Witness: structural navigation; subtree shape suffices for this boundary example.
-/
private theorem orphan_locations {address current producer owners}
    (known : Located orphanWork address current producer owners)
    : current = orphanWork
      ∨ current = .stream WorkQueueSemantics.node []
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
    : node = WorkQueueSemantics.node ∧ kind = .stream := by
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
    : NodeAccounted orphanWork WorkQueueSemantics.matching [] [] 0 := by
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
        Explains orphanWork [] [WorkQueueSemantics.node] events
          WorkQueueSemantics.matching []
        ∧ NodesTerminal orphanWork [0] WorkQueueSemantics.matching events []
        ∧ ¬Terminal orphanWork [0] WorkQueueSemantics.matching events [] := by
  have initial : Initializes orphanWork [] [WorkQueueSemantics.node] := by
    refine ⟨⟨by simp, by simp, ?_⟩, by simp⟩
    intro node member
    obtain rfl := List.mem_singleton.mp member
    refine ⟨[], none, .stream (.left .root), ?_⟩
    exact ⟨by simp [announcedRefs, pendingRefs],
      Or.inl ⟨WorkQueueSemantics.noFailure _ _, Or.inl rfl⟩, by simp, Or.inl rfl⟩
  have empty : Explains orphanWork [] [WorkQueueSemantics.node] [] WorkQueueSemantics.matching [] :=
    ⟨initial, by simp [FailureWitness], by simp⟩
  have allowed : EventAllowed orphanWork [0] WorkQueueSemantics.matching [] []
      (.streamSuccess WorkQueueSemantics.node) := by
    exact ⟨⟨[], none, .stream (.left .root)⟩,
      by simp [Open, announcedRefs, pendingRefs, completedRefs, WorkQueueSemantics.node],
      WorkQueueSemantics.noFailure _ _, orphan_accounted⟩
  refine ⟨[.streamSuccess WorkQueueSemantics.node], ?_, ?_, ?_⟩
  · simpa [WorkQueueSemantics.node, failedBefore] using empty.append_event allowed
  · intro node kind parents birth known
    obtain ⟨rfl, _⟩ := orphan_node known
    exact Or.inl (by simp [completedRefs, eventCompleted])
  · intro terminal
    have known : TaskAt orphanWork (.executionGroup [1]) [] none (.object [] (.ok ([], 0))) :=
      .executionGroup (.right .root)
    rcases terminal.1 _ _ _ _ known with cancelled | published
    · exact WorkQueueSemantics.noCancellation _ _ cancelled
    · rcases published with ⟨index, event, selected, value, _⟩
      cases index with
      | zero =>
          have same : event = .streamSuccess WorkQueueSemantics.node := by
            simpa using selected.symm
          subst event
          exact value
      | succ index => simp at selected

end GraphQL.IncrementalDelivery.Tests.Minimality
