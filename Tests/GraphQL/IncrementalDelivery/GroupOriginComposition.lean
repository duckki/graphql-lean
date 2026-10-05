import Proofs.GraphQL.IncrementalDelivery.Correctness.GroupOriginComposition

/-! Reused broad scopes and fresh child scopes take different structural origin witnesses. -/

namespace GraphQL.IncrementalDelivery.Tests.GroupOriginComposition
open GraphQL.IncrementalDelivery.Execution WorkQueueSemantics
open GraphQL.IncrementalDelivery.Correctness

private def broad : DeliveryNode := { ref := 1, path := [] }
private def narrow : DeliveryNode := { ref := 0, path := [.field "object"] }

private def fresh : DeliveryNode :=
  { ref := 1, path := [.field "object", .field "child"] }

private def result : Result (List (Name × ResponseValue)) := .ok ([], 0)

private def rootWork (node : DeliveryNode) : Work :=
  .executionGroup [⟨node, []⟩] node.path result .empty

private theorem root_origins (node : DeliveryNode)
    : GroupProducerOrigins (rootWork node) := by
  have origins : GroupOriginsExcept [] (rootWork node) :=
    GroupOriginsExcept.executionGroup (GroupOriginsExcept.empty []) (by
      intro node dependencies impossible
      exact (Correctness.GroupOriginComposition.no_group_empty impossible).elim)
  exact origins.resolve (by simp)

private def reused : Work :=
  .executionGroup [⟨narrow, []⟩] narrow.path result (rootWork broad)

private theorem reused_except : GroupOriginsExcept [broad.ref] reused := by
  apply GroupOriginsExcept.executionGroup ((root_origins broad).except [broad.ref])
  intro node dependencies known outside
  rcases Correctness.GroupOriginComposition.group_in_executionGroup known with
    ⟨group, member, same, _⟩ | ⟨producer, impossible⟩
  · have groupEq : group = ⟨broad, []⟩ := List.mem_singleton.mp member
    subst group
    subst node
    exact False.elim (outside (by simp))
  · exact (Correctness.GroupOriginComposition.no_group_empty impossible).elim

/-- A broad reused group uses the earlier root origin, not its narrower local producer.
Witness: the component certificate excludes the inherited ref, then composition resolves
that ref using the sibling root descriptor. No impossible narrow-to-broad prefix is used.
-/
theorem reused_scope_has_origin
    : GroupProducerOrigins (.combine (rootWork broad) reused) := by
  have origins := GroupOriginsExcept.combine_resolving (introduced := [broad.ref])
    ((root_origins broad).except []) (by simpa using reused_except) (by
      intro ref member
      have same : ref = broad.ref := List.mem_singleton.mp member
      subst ref
      exact GroupOrigin.executionGroup_root (groups := [⟨broad, []⟩])
        (group := ⟨broad, []⟩) (path := broad.path) (result := result)
        (children := .empty) (by simp))
  exact origins.resolve (by simp)

private def produced : Work :=
  .executionGroup [⟨narrow, []⟩] narrow.path result (rootWork fresh)

/-- A freshly introduced child group gets an earlier, scope-covering producer witness.
Witness: wrapping the child root relocates its birth to the parent task; the parent's ref
is smaller and its attachment is a prefix of the new group scope.
-/
theorem produced_scope_has_origin : GroupProducerOrigins produced := by
  have origins : GroupOriginsExcept [] produced :=
    GroupOriginsExcept.executionGroup ((root_origins fresh).except []) (by
      intro node dependencies known _
      rcases Correctness.GroupOriginComposition.group_in_executionGroup known with
        ⟨group, member, same, _⟩ | ⟨producer, impossible⟩
      · have groupEq : group = ⟨fresh, []⟩ := List.mem_singleton.mp member
        subst group
        subst node
        exact Or.inr ⟨narrow.ref, by simp, by decide, by decide⟩
      · exact (Correctness.GroupOriginComposition.no_group_empty impossible).elim)
  exact origins.resolve (by simp)

private def streamed : Work :=
  .stream narrow [(.ok (.object [], 0), rootWork fresh)]

/-- A defer introduced inside a streamed item uses that item's producer and list scope.
Witness: stream composition turns the child root into an indexed item-produced descriptor;
the stream ref is earlier, and its list attachment covers the child's scope.
-/
theorem streamed_scope_has_origin : GroupProducerOrigins streamed := by
  apply GroupProducerOrigins.stream
  · intro index result children entry
    have bound : index < 1 := (List.getElem?_eq_some_iff.mp entry).1
    have zero : index = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ bound)
    subst index
    have same : result = .ok (.object [], 0) ∧ children = rootWork fresh := by
      simpa using entry.symm
    rcases same with ⟨rfl, rfl⟩
    exact root_origins fresh
  · intro index result children node dependencies entry known
    have bound : index < 1 := (List.getElem?_eq_some_iff.mp entry).1
    have zero : index = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ bound)
    subst index
    have same : result = .ok (.object [], 0) ∧ children = rootWork fresh := by
      simpa using entry.symm
    rcases same with ⟨rfl, rfl⟩
    rcases Correctness.GroupOriginComposition.group_in_executionGroup known with
      ⟨group, member, same, _⟩ | ⟨producer, impossible⟩
    · have groupEq : group = ⟨fresh, []⟩ := List.mem_singleton.mp member
      subst group
      subst node
      exact ⟨by decide, by decide⟩
    · exact (Correctness.GroupOriginComposition.no_group_empty impossible).elim

/-- An exhausted stream has no group descriptor requiring a producer witness.
Witness: no indexed item can satisfy the composition premise.
-/
theorem empty_stream_has_origins : GroupProducerOrigins (.stream narrow []) := by
  apply GroupProducerOrigins.stream <;> intros <;> simp_all

#print axioms reused_scope_has_origin
#print axioms produced_scope_has_origin
#print axioms streamed_scope_has_origin
#print axioms empty_stream_has_origins
#print axioms GroupOriginsExcept.combine_resolving
#print axioms GroupOriginsExcept.executionGroup
#print axioms GroupProducerOrigins.stream

end GraphQL.IncrementalDelivery.Tests.GroupOriginComposition
