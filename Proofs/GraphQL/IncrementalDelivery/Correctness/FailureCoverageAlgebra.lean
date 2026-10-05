import Proofs.GraphQL.IncrementalDelivery.Correctness.ReferenceFailureCoverage
import Proofs.GraphQL.IncrementalDelivery.WorkQueueSemantics.StructuralEquivalence

/-! Structural algebra for the pure failure-aware execution comparison. -/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution
open WorkQueueSemantics

/-- Field-position projection distributes over appended response fields.
Witness: list descent, retaining nullable leaves and optional containers alike.
-/
theorem responsePositions_fields_append (containers : Bool) (path : ResponsePath)
    (left right : List (Name × ResponseValue))
    : ResponsePositions.fields containers path (left ++ right)
      = ResponsePositions.fields containers path left
        ++ ResponsePositions.fields containers path right := by
  induction left with
  | nil => rfl
  | cons head rest ih => simp [ResponsePositions.fields, ih, List.append_assoc]

/-- Field permutation preserves response-position membership, including all containers.
Witness: field projection is a flat map, so permutation transports each complete subtree.
-/
theorem responsePositions_fields_perm (containers : Bool) (path : ResponsePath)
    {left right : List (Name × ResponseValue)} (permuted : left.Perm right)
    : (ResponsePositions.fields containers path left).Perm
        (ResponsePositions.fields containers path right) := by
  have flatten (fields : List (Name × ResponseValue))
      : ResponsePositions.fields containers path fields
        = fields.flatMap (fun field =>
            ResponsePositions.value containers (path ++ [.field field.1]) field.2) := by
    induction fields with
    | nil => rfl
    | cons field rest ih => simp [ResponsePositions.fields, ih]
  rw [flatten, flatten]
  exact permuted.flatMap _

-----------------------------------------------------------------------------------------
-- Source positions do not depend on proof-only occurrence labels
-----------------------------------------------------------------------------------------

mutual
  /-- Relabelling source occurrences preserves every response position.
  Witness: mutual descent through work and streamed items; cursors and payloads are fixed.
  -/
  theorem sourceTasks_positions_relabel (containers : Bool) (work : Work)
      (cursors : ResponsePositions.Cursors) (address other : Address)
      (producer parent : Option Occurrence)
      : (sourceTasks address producer cursors work).flatMap
          (SourceTask.positions containers)
        = (sourceTasks other parent cursors work).flatMap
            (SourceTask.positions containers) := by
    cases work with
    | empty => rfl
    | combine left right =>
        simp only [sourceTasks, List.flatMap_append]
        rw [sourceTasks_positions_relabel containers left cursors (address ++ [0])
          (other ++ [0]) producer parent,
          sourceTasks_positions_relabel containers right cursors (address ++ [1])
            (other ++ [1]) producer parent]
    | executionGroup groups path result children =>
        simp only [sourceTasks, List.flatMap_cons, SourceTask.positions, SourceTask.cursors]
        rw [sourceTasks_positions_relabel containers children _ (address ++ [0])
          (other ++ [0]) (some (.executionGroup address)) (some (.executionGroup other))]
    | stream node items =>
        exact sourceItemTasks_positions_relabel containers items node _ 0 address other
          producer parent
  termination_by sizeOf work

  /-- Item positions are unchanged by relabelling their structural source occurrences.
  Witness: each payload has the same absolute item index and seeds the same child cursors.
  -/
  theorem sourceItemTasks_positions_relabel (containers : Bool)
      (items : List (Result ResponseValue × Work)) (node : DeliveryNode)
      (index ordinal : Nat) (address other : Address)
      (producer parent : Option Occurrence)
      : (sourceItemTasks address producer node index ordinal items).flatMap
          (SourceTask.positions containers)
        = (sourceItemTasks other parent node index ordinal items).flatMap
            (SourceTask.positions containers) := by
    cases items with
    | nil => rfl
    | cons head tail =>
        obtain ⟨result, children⟩ := head
        simp only [sourceItemTasks, List.flatMap_cons, List.flatMap_append,
          SourceTask.positions, SourceTask.cursors]
        rw [sourceTasks_positions_relabel containers children _ (address ++ [ordinal])
          (other ++ [ordinal]) (some (.item address ordinal)) (some (.item other ordinal)),
          sourceItemTasks_positions_relabel containers tail node (index + 1)
            (ordinal + 1) address other producer parent]
  termination_by sizeOf items
end

-----------------------------------------------------------------------------------------
-- Retained failure witnesses survive embedding in a larger work tree
-----------------------------------------------------------------------------------------

private theorem located_embed {work address current producer owners}
    (known : StructuralEquivalence.Located work address current producer owners)
    {root route enclosing dependencies}
    (embedded : StructuralEquivalence.Located root route work enclosing dependencies)
    : ∃ parent refs,
        StructuralEquivalence.Located root (route ++ address) current parent refs := by
  induction known with
  | root => exact ⟨_, _, by simpa using embedded⟩
  | left _ ih =>
      obtain ⟨parent, refs, found⟩ := ih
      exact ⟨_, _, by simpa [List.append_assoc] using found.left⟩
  | right _ ih =>
      obtain ⟨parent, refs, found⟩ := ih
      exact ⟨_, _, by simpa [List.append_assoc] using found.right⟩
  | executionGroup _ ih =>
      obtain ⟨parent, refs, found⟩ := ih
      exact ⟨_, _, by simpa [List.append_assoc] using found.executionGroup⟩
  | item _ entry ih =>
      obtain ⟨parent, refs, found⟩ := ih
      exact ⟨_, _, by simpa [List.append_assoc] using found.item entry⟩

/-- An embedded task retains its payload, without asserting unchanged producer labels.
Witness: structural location induction, followed by the same group/item lookup.
-/
theorem TaskAt.in_located {work occurrence owners producer payload}
    (known : TaskAt work occurrence owners producer payload)
    {root route enclosing dependencies}
    (embedded : Located root route work enclosing dependencies)
    : ∃ occurrence owners producer, TaskAt root occurrence owners producer payload := by
  have base := StructuralEquivalence.located_of_current embedded
  cases StructuralEquivalence.taskAt_of_current known with
  | executionGroup located =>
      obtain ⟨parent, refs, found⟩ := located_embed located base
      exact ⟨_, _, _, (StructuralEquivalence.TaskAt.executionGroup found).toCurrent⟩
  | item located entry =>
      obtain ⟨parent, refs, found⟩ := located_embed located base
      exact ⟨_, _, _, (StructuralEquivalence.TaskAt.item found entry).toCurrent⟩

/-- A failure witness in the left component remains a task of the combined work.
Witness: embedding at the left structural edge, preserving the failing payload.
-/
theorem TaskAt.in_combine_left {work occurrence owners producer payload}
    (known : TaskAt work occurrence owners producer payload) (right : Work)
    : ∃ occurrence owners producer,
        TaskAt (.combine work right) occurrence owners producer payload :=
  TaskAt.in_located known (StructuralEquivalence.Located.left .root).toCurrent

/-- A failure witness in the right component remains a task of the combined work.
Witness: embedding at the right structural edge, preserving the failing payload.
-/
theorem TaskAt.in_combine_right {work occurrence owners producer payload}
    (known : TaskAt work occurrence owners producer payload) (left : Work)
    : ∃ occurrence owners producer,
        TaskAt (.combine left work) occurrence owners producer payload :=
  TaskAt.in_located known (StructuralEquivalence.Located.right .root).toCurrent

-----------------------------------------------------------------------------------------
-- Adding retained work preserves an existing prepared-response explanation
-----------------------------------------------------------------------------------------

/-- Additional right-hand work cannot lose an existing coverage explanation.
Witness: source positions retain their cursors under relabelling; failures embed on the
left edge. The ordinary reference and initial response are unchanged.
-/
theorem PreparedResponseCovers.combine_left {reference response work containers}
    (covered : PreparedResponseCovers reference response work containers) (right : Work)
    : PreparedResponseCovers reference response (.combine work right) containers := by
  intro path member
  rcases covered path member with delivered | failed
  · simp only [List.mem_append] at delivered
    rcases delivered with initial | future
    · exact Or.inl (List.mem_append_left _ initial)
    · have relabelled := sourceTasks_positions_relabel containers work
        (ResponsePositions.listCursors [] response.data) [] [0] none none
      rw [relabelled] at future
      exact Or.inl (List.mem_append_right _
        (by simpa only [sourceTasks, List.flatMap_append, List.mem_append, List.nil_append] using
          (Or.inl future : _ ∨ _)))
  · obtain ⟨occurrence, owners, producer, payload, known, fails, related⟩ := failed
    obtain ⟨occurrence, owners, producer, embedded⟩ := TaskAt.in_combine_left known right
    exact Or.inr ⟨occurrence, owners, producer, payload, embedded, fails, related⟩

/-- Additional left-hand work cannot lose an existing coverage explanation.
Witness: source relabelling on the right edge and payload-preserving failure embedding.
-/
theorem PreparedResponseCovers.combine_right {reference response work containers}
    (covered : PreparedResponseCovers reference response work containers) (left : Work)
    : PreparedResponseCovers reference response (.combine left work) containers := by
  intro path member
  rcases covered path member with delivered | failed
  · simp only [List.mem_append] at delivered
    rcases delivered with initial | future
    · exact Or.inl (List.mem_append_left _ initial)
    · have relabelled := sourceTasks_positions_relabel containers work
        (ResponsePositions.listCursors [] response.data) [] [1] none none
      rw [relabelled] at future
      exact Or.inl (List.mem_append_right _
        (by simpa only [sourceTasks, List.flatMap_append, List.mem_append, List.nil_append] using
          (Or.inr future : _ ∨ _)))
  · obtain ⟨occurrence, owners, producer, payload, known, fails, related⟩ := failed
    obtain ⟨occurrence, owners, producer, embedded⟩ := TaskAt.in_combine_right known left
    exact Or.inr ⟨occurrence, owners, producer, payload, embedded, fails, related⟩

-----------------------------------------------------------------------------------------
-- Existing ordinary null ancestors are explained by retained descendant failures
-----------------------------------------------------------------------------------------

/-- A retained failed task explains an ordinary null root, at any descendant attachment.
Witness: the reference has exactly the root null position, which prefixes every payload
attachment. This constructs the null-ancestor branch without a notice or scheduler law.
-/
theorem preparedResponseCovers_null_of_failedTask
    {work occurrence owners producer payload}
    (known : TaskAt work occurrence owners producer payload)
    (fails : payload.failure.isSome = true) (response : Response) (containers : Bool)
    : PreparedResponseCovers .null response work containers := by
  intro path member
  simp only [ResponsePositions.value, List.mem_singleton] at member
  subst path
  exact Or.inr
    ⟨occurrence, owners, producer, payload, known, fails, Or.inr ⟨rfl, by simp⟩⟩

/-- A failed descendant explains a single ordinary null field beneath an initial object.
Witness: the object root is initially present; its null field is an existing reference
position above the real task attachment. Initial object fields and counted errors are
otherwise unrestricted. Names here are response aliases, not schema field names.
-/
theorem preparedResponseCovers_nullField_of_failedTask
    {work occurrence owners producer payload}
    (known : TaskAt work occurrence owners producer payload)
    (fails : payload.failure.isSome = true) (name : Name)
    (below : [ResponsePathSegment.field name].IsPrefix payload.path)
    (initial : List (Name × ResponseValue)) (errors : Nat) (containers : Bool)
    : PreparedResponseCovers (.object [(name, .null)])
        { data := .object initial, errors := errors } work containers := by
  intro path member
  simp only [ResponsePositions.value, ResponsePositions.fields, List.append_nil,
    List.nil_append, List.mem_append, List.mem_singleton] at member
  rcases member with root | nullField
  · exact Or.inl (List.mem_append_left _ (List.mem_append_left _ root))
  · subst path
    exact Or.inr ⟨occurrence, owners, producer, payload, known, fails,
      Or.inr ⟨by simp [GraphQL.Execution.ResponseValue.isNullAt], below⟩⟩

end GraphQL.IncrementalDelivery.Correctness
