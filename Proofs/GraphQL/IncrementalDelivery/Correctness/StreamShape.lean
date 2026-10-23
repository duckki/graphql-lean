import Proofs.GraphQL.IncrementalDelivery.Correctness.OwnerAvailability
import Proofs.GraphQL.IncrementalDelivery.Semantics.WorkSize

/-! Structural facts for stream-only work, independent of progress and reporting. -/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Semantics
open WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Stream-only work has no deferred dependencies
-----------------------------------------------------------------------------------------

/-- The finite work contains streams, combinations, and empty subwork, but no deferred task.
Item outcomes, errors, nesting depth, and branching are unrestricted.
-/
def StreamOnly : Work → Prop
  | .empty => True
  | .declareGroups _ tasks => StreamOnly tasks
  | .combine left right => StreamOnly left ∧ StreamOnly right
  | .executionGroup .. => False
  | .stream _ items => ∀ entry ∈ items, StreamOnly entry.2
termination_by work => sizeOf work
decreasing_by
  all_goals simp_wf
  all_goals try decreasing_trivial
  have smaller := List.sizeOf_lt_of_mem ‹entry ∈ items›
  have pairSize : sizeOf entry = 1 + sizeOf entry.1 + sizeOf entry.2 :=
    Prod.mk.sizeOf_spec _ _
  omega

/-- Declaration annotations do not introduce deferred tasks. -/
theorem StreamOnly.withoutDeclarations {work : Work} (known : StreamOnly work)
    : StreamOnly work.withoutDeclarations := by
  cases work with
  | declareGroups groups tasks =>
      simpa only [StreamOnly, Work.withoutDeclarations]
        using StreamOnly.withoutDeclarations (work := tasks)
          (by simpa only [StreamOnly] using known)
  | _ => simpa only [Work.withoutDeclarations] using known
termination_by work

/-- Every location in stream-only work is stream-only and has no enclosing defer refs.
Witness: structural navigation; stream-item edges reset enclosing owners to empty.
-/
theorem StreamOnly.located {work address current producer owners}
    (onlyStreams : StreamOnly work)
    (located : Located work address current producer owners)
    : StreamOnly current ∧ owners = [] := by
  have navigation := StructuralEquivalence.located_of_current located
  clear located
  induction navigation with
  | root => exact ⟨onlyStreams.withoutDeclarations, rfl⟩
  | left _ ih =>
      rw [StreamOnly] at ih
      exact ⟨ih.1.1.withoutDeclarations, ih.2⟩
  | right _ ih =>
      rw [StreamOnly] at ih
      exact ⟨ih.1.2.withoutDeclarations, ih.2⟩
  | executionGroup _ ih => exact False.elim (by simpa only [StreamOnly] using ih.1)
  | item _ entry ih =>
      rw [StreamOnly] at ih
      exact ⟨(ih.1 _ (List.mem_of_getElem? entry)).withoutDeclarations, rfl⟩

/-- Every stream-only task has a single stream owner without defer dependencies.
Witness: its item descriptor and the empty enclosing-owner context at its location.
-/
theorem StreamOnly.task {work occurrence owners producer payload}
    (onlyStreams : StreamOnly work)
    (known : TaskAt work occurrence owners producer payload)
    : ∃ node result,
        owners = [node.ref]
        ∧ payload = .item node result
        ∧ NodeAt work node .stream [] producer := by
  cases StructuralEquivalence.taskAt_of_current known with
  | executionGroup located =>
      exact False.elim
        (by simpa only [StreamOnly] using (onlyStreams.located located.toCurrent).1)
  | item located selected =>
      have empty := (onlyStreams.located located.toCurrent).2
      exact ⟨_, _, rfl, rfl, empty ▸ NodeAt.stream located.toCurrent⟩

/-- A descriptor in stream-only work is a stream with no deferred dependency refs.
Witness: its located boundary cannot be deferred and has an empty owner context.
-/
theorem StreamOnly.node {work node kind dependencies producer}
    (onlyStreams : StreamOnly work)
    (known : NodeAt work node kind dependencies producer)
    : kind = .stream ∧ dependencies = [] := by
  cases StructuralEquivalence.nodeAt_of_current known with
  | group located member =>
      exact False.elim
        (by simpa only [StreamOnly] using (onlyStreams.located located.toCurrent).1)
  | stream located => exact ⟨rfl, (onlyStreams.located located.toCurrent).2⟩

/-- Nonempty stream-only subwork has a first stream with the location's producer.
Witness: descend through combine nodes only, stopping before the first stream's items.
-/
theorem StreamOnly.first_stream {work address current producer owners}
    (onlyStreams : StreamOnly current)
    (nonempty : current.size ≠ 0)
    (located : Located work address current.withoutDeclarations producer owners)
    : ∃ node, NodeAt work node .stream owners producer := by
  cases current with
  | empty => exact False.elim (nonempty rfl)
  | declareGroups groups tasks =>
      apply StreamOnly.first_stream (current := tasks)
        (by simpa only [StreamOnly] using onlyStreams)
        (by simpa only [Work.size] using nonempty) located
  | executionGroup => simp only [StreamOnly] at onlyStreams
  | stream node items => exact ⟨node, .stream located⟩
  | combine left right =>
      rw [StreamOnly] at onlyStreams
      by_cases empty : left.size = 0
      · apply onlyStreams.2.first_stream (located := .right located)
        simpa only [Work.size, empty, Nat.zero_add] using nonempty
      · exact onlyStreams.1.first_stream empty (.left located)
termination_by sizeOf current

end GraphQL.IncrementalDelivery.Correctness
