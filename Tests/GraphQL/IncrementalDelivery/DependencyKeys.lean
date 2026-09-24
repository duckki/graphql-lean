import Proofs.GraphQL.IncrementalDelivery.Correctness.LeastKeyProgress
import Tests.GraphQL.IncrementalDelivery.CursorOrigins

/-! Dependency-key progress across a deferred producer and its nested stream. -/

namespace GraphQL.IncrementalDelivery.Tests.DependencyKeys
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Semantics
open Semantics.Ancestry Semantics.GeneralScheduling
open WorkScheduler

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

/-- An uncancelled nested stream task has a healthy producer owner with no larger key.
Witness: generated metadata, even with arbitrary recorded failure evidence.
-/
example (failed : List Occurrence)
    (healthy : ¬NodeFailed CursorOrigins.nested failed 1)
    (active : ¬TaskCancelled CursorOrigins.nested failed (.item [0] 0))
    : ∃ owners ancestor result key,
        TaskAt CursorOrigins.nested (.executionGroup []) owners ancestor result
        ∧ key ∈ owners
        ∧ ¬NodeFailed CursorOrigins.nested failed key
        ∧ key ≤ 1 := by
  apply producer_owner_key_le nested_metadata.1 nested_metadata.2.1 nested_metadata.2.2.1
    nested_metadata.2.2.2 (TaskAt.item (.executionGroup .root) rfl)
    (by simp [CursorOrigins.child]) healthy active

/-- An initially blocked stream item finds ready work without increasing its owner key.
Witness: descend to its unpublished deferred producer; no history is selected or supplied.
-/
example
    : ∃ occurrence owners producer payload key,
        TaskAt CursorOrigins.nested occurrence owners producer payload
        ∧ CanPublish CursorOrigins.nested (fun _ => .executionGroup []) [] [] occurrence
            producer
        ∧ key ∈ owners
        ∧ ¬NodeFailed CursorOrigins.nested [] key
        ∧ key ≤ 1 := by
  apply readyTask_owner_key_le nested_metadata.1 nested_metadata.2.1
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
