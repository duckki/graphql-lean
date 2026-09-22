import Proofs.GraphQL.IncrementalDelivery.Correctness.LeastKeyProgress
import Tests.GraphQL.IncrementalDelivery.CursorOrigins

/-! Dependency-key progress across a deferred producer and its nested stream. -/

namespace GraphQL.IncrementalDelivery.Tests.DependencyKeys
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Semantics
open Semantics.Ancestry Semantics.GeneralScheduling
open WorkQueueSemantics

/-- This deferred-to-stream fixture has the generated key-order and continuity shape.
Witness: root key zero precedes the nested stream key one; its only child work is empty.
-/
theorem nested_metadata
    : Valid (fun _ => []) 2
      ∧ MixedKeys.WorkAt (fun _ => []) 0 2 CursorOrigins.nested
      ∧ DeferContinuous (fun _ => []) CursorOrigins.nested
      ∧ StreamOwnersOrdered CursorOrigins.nested := by
  simp [Valid, MixedKeys.WorkAt, DeferContinuous, DeferUnder, StreamOwnersOrdered,
    OwnersBefore, FragmentAt, CursorOrigins.nested, CursorOrigins.parent,
    CursorOrigins.child]

/-- While a nested task and its producer are unpublished, an uncancelled child with a
healthy owner has a healthy producer owner with no larger key. Witness: generated
metadata and an explained failure-cut history.
-/
example {groups streams matching events failures}
    (explained : Explains CursorOrigins.nested groups streams events matching failures)
    (healthy : ¬NodeFailed CursorOrigins.nested matching events failures 1)
    (fresh : ¬Published matching events (.item [0] 0))
    (parentFresh : ¬Published matching events (.executionGroup []))
    (active : ¬TaskCancelled CursorOrigins.nested matching events failures (.item [0] 0))
    : ∃ owners ancestor result key,
        TaskAt CursorOrigins.nested (.executionGroup []) owners ancestor result
        ∧ key ∈ owners
        ∧ ¬NodeFailed CursorOrigins.nested matching events failures key
        ∧ key ≤ 1 := by
  apply producer_owner_key_le explained nested_metadata.1 nested_metadata.2.1
    nested_metadata.2.2.1
    nested_metadata.2.2.2 (TaskAt.item (.executionGroup .root) rfl)
    (by simp [CursorOrigins.child]) healthy fresh parentFresh active

/-- The deferred root is an eligible initial frontier for the nested-stream fixture.
Witness: its root task is outstanding and no failure cut has been recorded.
-/
private theorem nested_initialized
    : Initializes CursorOrigins.nested [CursorOrigins.parent] [] := by
  refine ⟨⟨by simp, ?_, by simp⟩, by simp⟩
  intro node member
  have same := List.mem_singleton.mp member
  subst node
  refine ⟨
    [],
    none,
    .group (group := { node := CursorOrigins.parent }) .root (by simp),
    ?_,
    Or.inl ⟨fun failure => failure.nonempty rfl, Or.inr ?_⟩,
    by simp,
    by simp
  ⟩
  · simp [announcedKeys, pendingKeys]
  · intro accounted
    have impossible := accounted (.executionGroup []) [0]
      ⟨none, _, TaskAt.executionGroup Located.root⟩ (by simp [CursorOrigins.parent])
    rcases impossible with cancelled | published
    · exact cancelled.nonempty rfl
    · simp [Published] at published

/-- An initially blocked stream item finds ready work without increasing its owner key.
Witness: descend to its unpublished deferred producer from the explained initial prefix.
-/
example
    : ∃ occurrence owners producer payload key,
        TaskAt CursorOrigins.nested occurrence owners producer payload
        ∧ CanPublish CursorOrigins.nested (fun _ => .executionGroup []) [] [] occurrence
            producer
        ∧ key ∈ owners
        ∧ ¬NodeFailed CursorOrigins.nested (fun _ => .executionGroup []) [] [] key
        ∧ key ≤ 1 := by
  have initial : Explains CursorOrigins.nested [CursorOrigins.parent] [] []
      (fun _ => .executionGroup []) [] :=
    ⟨nested_initialized, by simp [FailureWitness], by simp⟩
  apply readyTask_owner_key_le initial nested_metadata.1 nested_metadata.2.1
    nested_metadata.2.2.1 nested_metadata.2.2.2
    (TaskAt.item (index := 0) (.executionGroup .root) rfl) (by simp [CursorOrigins.child])
    (fun failure => failure.nonempty rfl)
  rintro (cancelled | published)
  · exact cancelled.nonempty rfl
  · simp [Published] at published

/-- A task owner descriptor is located at that task's actual producer boundary.
Witness: the strengthened structural owner projection retains producer identity.
-/
example
    : ∃ node kind parents,
        NodeAt CursorOrigins.nested node kind parents (some (.executionGroup []))
        ∧ node.key = 1 :=
  (TaskAt.item (index := 0) (.executionGroup .root) rfl).owner_at_producer
    (by simp [CursorOrigins.child])

end GraphQL.IncrementalDelivery.Tests.DependencyKeys
