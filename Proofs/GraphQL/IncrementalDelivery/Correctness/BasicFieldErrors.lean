import Proofs.GraphQL.IncrementalDelivery.Correctness.BasicFieldPartitions

/-! Ordinary field partitions preserve bubbling and error counts, not only success. -/

namespace GraphQL.IncrementalDelivery.Correctness.TypedResponse
open GraphQL.IncrementalDelivery.Execution

/-- Proof-only field-result equivalence preserves failure or successful field permutation,
with the same counted errors. Neither outcome is assumed successful or error-free.
-/
def FieldResultsEquivalent (left right : Result (List (Name × ResponseValue))) : Prop :=
  match left, right with
  | .error errors, .error more => errors = more
  | .ok (data, errors), .ok (other, more) => data.Perm other ∧ errors = more
  | _, _ => False

/-- Field-result equivalence is reflexive by outcome inspection. -/
theorem FieldResultsEquivalent.refl (result : Result (List (Name × ResponseValue)))
    : FieldResultsEquivalent result result := by
  cases result <;> simp [FieldResultsEquivalent]

/-- Field-result equivalence composes by error equality or field permutation. -/
theorem FieldResultsEquivalent.trans {left middle right}
    (first : FieldResultsEquivalent left middle)
    (second : FieldResultsEquivalent middle right)
    : FieldResultsEquivalent left right := by
  cases left <;> cases middle <;> cases right
  all_goals simp only [FieldResultsEquivalent] at *
  all_goals
    first
      | contradiction
      | exact first.trans second
      | exact ⟨first.1.trans second.1, first.2.trans second.2⟩

/-- Combining equivalent field results preserves permutation and bubbling error totals.
Witness: inspect the four combinations; successful data concatenate by permutation.
-/
theorem FieldResultsEquivalent.combine {left otherLeft right otherRight}
    (leftEq : FieldResultsEquivalent left otherLeft)
    (rightEq : FieldResultsEquivalent right otherRight)
    : FieldResultsEquivalent (GraphQL.Execution.Result.combine List.append left right)
        (GraphQL.Execution.Result.combine List.append otherLeft otherRight) := by
  cases left <;> cases otherLeft <;> cases right <;> cases otherRight
  all_goals simp only [GraphQL.Execution.Result.combine, FieldResultsEquivalent] at *
  all_goals
    first
      | contradiction
      | exact ⟨leftEq.1.append rightEq.1, by omega⟩
      | omega

/-- Field-result append is associative including bubbling and accumulated errors.
Witness: the eight result combinations reduce to list and count associativity.
-/
theorem fieldResults_combine_assoc
    (left middle right : Result (List (Name × ResponseValue)))
    : GraphQL.Execution.Result.combine List.append
        (GraphQL.Execution.Result.combine List.append left middle) right
      = GraphQL.Execution.Result.combine List.append left
          (GraphQL.Execution.Result.combine List.append middle right) := by
  cases left <;> cases middle <;> cases right <;>
    simp [GraphQL.Execution.Result.combine, List.append_assoc, Nat.add_assoc]

/-- Exchanging two field partitions preserves data permutation and counted errors.
Witness: successful data commute up to permutation; bubbling sums commute exactly.
-/
theorem fieldResults_combine_comm (left right : Result (List (Name × ResponseValue)))
    : FieldResultsEquivalent (GraphQL.Execution.Result.combine List.append left right)
        (GraphQL.Execution.Result.combine List.append right left) := by
  cases left <;> cases right <;>
    simp [GraphQL.Execution.Result.combine, FieldResultsEquivalent, Nat.add_comm,
      List.perm_append_comm]

/-- Ordinary execution of appended field groups is result combination even with errors.
Witness: group-list induction and result associativity retain bubbling and error totals.
-/
theorem basicFields_append_result (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues) (fuel : Nat) (parentType : Name)
    (source : ResolverValue ObjectRef)
    (left right : List (Name × List GraphQL.Execution.ExecutableField))
    : GraphQL.Execution.executeCollectedFields schema resolvers variables fuel parentType
        source (left ++ right)
      = GraphQL.Execution.Result.combine List.append
          (GraphQL.Execution.executeCollectedFields schema resolvers variables fuel
            parentType source left)
          (GraphQL.Execution.executeCollectedFields schema resolvers variables fuel
            parentType source right) := by
  induction left with
  | nil =>
      cases result : GraphQL.Execution.executeCollectedFields schema resolvers variables fuel
          parentType source right <;>
        simp [GraphQL.Execution.executeCollectedFields, GraphQL.Execution.Result.combine,
          result]
  | cons head tail ih =>
      rcases head with ⟨name, fields⟩
      simp only [List.cons_append, GraphQL.Execution.executeCollectedFields, ih,
        fieldResults_combine_assoc]

/-- Permuting ordinary field groups preserves failure/success and the exact error count.
Witness: permutation induction; adjacent exchanges commute result combination, while
list/result associativity transports the unchanged tail. No zero-error premise is used.
-/
theorem basicFields_perm_withErrors (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues) (fuel : Nat) (parentType : Name)
    (source : ResolverValue ObjectRef)
    {left right : List (Name × List GraphQL.Execution.ExecutableField)}
    (permuted : left.Perm right)
    : FieldResultsEquivalent
        (GraphQL.Execution.executeCollectedFields schema resolvers variables fuel
          parentType source left)
        (GraphQL.Execution.executeCollectedFields schema resolvers variables fuel
          parentType source right) := by
  induction permuted with
  | nil => exact .refl _
  | cons head _ ih =>
      rcases head with ⟨name, fields⟩
      simp only [GraphQL.Execution.executeCollectedFields]
      exact (FieldResultsEquivalent.refl _).combine ih
  | swap left right tail =>
      rcases left with ⟨leftName, leftFields⟩
      rcases right with ⟨rightName, rightFields⟩
      simp only [GraphQL.Execution.executeCollectedFields]
      rw [← fieldResults_combine_assoc, ← fieldResults_combine_assoc]
      exact (fieldResults_combine_comm _ _).combine (.refl _)
  | trans _ _ first second => exact first.trans second

/-- A nonbubbling ordinary field result contains every field's typed entries, even when
nullable descendants counted errors. Witness: field-list induction; an error branch would
bubble instead of producing the given result. No zero-error premise is used.
-/
theorem basicFields_entries_withErrors (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues) (fuel : Nat) (parentType : Name)
    (source : ResolverValue ObjectRef) (path : ResponsePath)
    (groups : List (Name × List GraphQL.Execution.ExecutableField))
    (data : List (Name × ResponseValue)) (errors : Nat)
    (completed
      : GraphQL.Execution.executeCollectedFields schema resolvers variables fuel
          parentType source groups
        = .ok (data, errors))
    : fields path data
      = groups.flatMap
          (fun group =>
            result (fields path)
              (GraphQL.Execution.executeField schema resolvers variables fuel parentType
                source group.1 group.2)) := by
  induction groups generalizing data errors with
  | nil =>
      simp [GraphQL.Execution.executeCollectedFields] at completed
      rw [completed.1]
      rfl
  | cons head tail ih =>
      rcases head with ⟨name, selections⟩
      cases left : GraphQL.Execution.executeField schema resolvers variables fuel
          parentType source name selections <;>
        cases right : GraphQL.Execution.executeCollectedFields schema resolvers variables fuel
          parentType source tail <;>
        simp only [GraphQL.Execution.executeCollectedFields, left, right,
          GraphQL.Execution.Result.combine, Except.ok.injEq, Prod.mk.injEq,
          reduceCtorEq] at completed
      obtain ⟨rfl, _⟩ := completed
      rename_i headData tailData countEq
      apply (fields_append path headData.1 tailData.1).trans
      simp only [List.flatMap_cons, left, result]
      exact congrArg (List.append _) (ih _ _ right)

/-- Reordered nonbubbling field groups retain typed entries and their counted errors.
Witness: arbitrary-error result permutation supplies the reordered successful outcome;
the exact entry formula transports the group permutation, including nullable error data.
-/
theorem basicFields_perm_entries_withErrors (schema : Schema)
    (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
    (parentType : Name) (source : ResolverValue ObjectRef) (path : ResponsePath)
    {left right : List (Name × List GraphQL.Execution.ExecutableField)}
    (permuted : left.Perm right) {data errors}
    (completed
      : GraphQL.Execution.executeCollectedFields schema resolvers variables fuel
          parentType source left
        = .ok (data, errors))
    : ∃ other,
        GraphQL.Execution.executeCollectedFields schema resolvers variables fuel
            parentType source right
          = .ok (other, errors)
        ∧ (fields path data).Perm (fields path other) := by
  have equivalent := basicFields_perm_withErrors schema resolvers variables fuel parentType
    source permuted
  rw [completed] at equivalent
  cases output
        : GraphQL.Execution.executeCollectedFields schema resolvers variables fuel
            parentType source right with
  | error count => simp [output, FieldResultsEquivalent] at equivalent
  | ok pair =>
      rcases pair with ⟨other, count⟩
      simp only [output, FieldResultsEquivalent] at equivalent
      have sameCount := equivalent.2
      subst count
      refine ⟨other, rfl, ?_⟩
      rw [basicFields_entries_withErrors schema resolvers variables fuel parentType source
          path left data errors completed,
        basicFields_entries_withErrors schema resolvers variables fuel parentType source
          path right other errors output]
      exact permuted.flatMap_right _

/-- An ordinary field collection bubbles exactly when one completed field bubbles.
Witness: field-list induction and result combination. This identifies an actual failing
field, independently of order, counts, or nullable fields that still return response data.
-/
theorem basicFields_bubbles_iff (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues) (fuel : Nat) (parentType : Name)
    (source : ResolverValue ObjectRef)
    (groups : List (Name × List GraphQL.Execution.ExecutableField))
    : (∃ errors,
        GraphQL.Execution.executeCollectedFields schema resolvers variables fuel
          parentType source groups
        = .error errors)
      ↔ ∃ group ∈ groups,
          ∃ errors,
            GraphQL.Execution.executeField schema resolvers variables fuel parentType
              source group.1 group.2
            = .error errors := by
  induction groups with
  | nil => simp [GraphQL.Execution.executeCollectedFields]
  | cons head tail ih =>
      rcases head with ⟨name, selections⟩
      simp only [List.mem_cons, or_and_right, exists_or, exists_eq_left]
      rw [← ih]
      cases left : GraphQL.Execution.executeField schema resolvers variables fuel parentType
          source name selections <;>
        cases right : GraphQL.Execution.executeCollectedFields schema resolvers variables fuel
          parentType source tail <;>
        simp [GraphQL.Execution.executeCollectedFields, GraphQL.Execution.Result.combine,
          left, right]

end GraphQL.IncrementalDelivery.Correctness.TypedResponse
