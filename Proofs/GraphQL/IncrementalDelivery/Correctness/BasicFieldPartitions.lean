import Proofs.GraphQL.IncrementalDelivery.Correctness.TypedResponse
import Proofs.GraphQL.IncrementalDelivery.Semantics.Planning

/-! Ordinary successful field execution respects permutations and partitions. -/

namespace GraphQL.IncrementalDelivery.Correctness.TypedResponse

open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Semantics

variable {ObjectRef : Type}

/-- A field collection succeeds with zero errors exactly when each field does; witness:
result combination. -/
theorem basicFields_success_iff (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues) (fuel : Nat) (parentType : Name)
    (source : ResolverValue ObjectRef)
    (groups : List (Name × List GraphQL.Execution.ExecutableField))
    : (∃ data,
        GraphQL.Execution.executeCollectedFields schema resolvers variables fuel
          parentType source groups
        = .ok (data, 0))
      ↔ ∀ group ∈ groups,
          ∃ data,
            GraphQL.Execution.executeField schema resolvers variables fuel
              parentType source group.1 group.2
            = .ok (data, 0) := by
  induction groups with
  | nil => simp [GraphQL.Execution.executeCollectedFields]
  | cons group rest ih =>
      rcases group with ⟨name, selected⟩
      simp only [List.forall_mem_cons, GraphQL.Execution.executeCollectedFields]
      rw [← ih]
      cases hh : GraphQL.Execution.executeField schema resolvers variables fuel
        parentType source name selected <;>
        cases ht : GraphQL.Execution.executeCollectedFields schema resolvers variables fuel
          parentType source rest <;>
        simp [GraphQL.Execution.Result.combine, Prod.ext_iff,
          Nat.add_eq_zero_iff]

/-- Successful basic field execution concatenates each group's typed entries, by list
induction. -/
theorem basicFields_entries (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues) (fuel : Nat) (parentType : Name)
    (source : ResolverValue ObjectRef) (path : ResponsePath)
    (groups : List (Name × List GraphQL.Execution.ExecutableField))
    (data : List (Name × ResponseValue))
    (h
      : GraphQL.Execution.executeCollectedFields schema resolvers variables fuel
          parentType source groups
        = .ok (data, 0))
    : fields path data
      = groups.flatMap
          (fun group =>
            result (fields path)
              (GraphQL.Execution.executeField schema resolvers variables fuel parentType
                source group.1 group.2)) := by
  induction groups generalizing data with
  | nil =>
      simp [GraphQL.Execution.executeCollectedFields] at h
      subst data
      rfl
  | cons group rest ih =>
      rcases group with ⟨name, selected⟩
      have hs := (basicFields_success_iff schema resolvers variables fuel parentType source
        ((name, selected) :: rest)).mp ⟨data, h⟩
      obtain ⟨head, hh⟩ := hs (name, selected) (by simp)
      obtain ⟨tail, ht⟩ :=
        (basicFields_success_iff schema resolvers variables fuel parentType source rest).mpr
          (fun g hg => hs g (by simp [hg]))
      simp only [GraphQL.Execution.executeCollectedFields, hh, ht,
        GraphQL.Execution.Result.combine, Nat.zero_add, Except.ok.injEq,
        Prod.mk.injEq, and_true] at h
      subst data
      simp [fields_append, List.flatMap_cons, hh, result, ih _ ht]

/-- Permuting successful field groups permutes their entries, preserving zero-error
execution. -/
theorem basicFields_perm (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues) (fuel : Nat) (parentType : Name)
    (source : ResolverValue ObjectRef) (path : ResponsePath)
    (left right : List (Name × List GraphQL.Execution.ExecutableField))
    (hp : left.Perm right) (data : List (Name × ResponseValue))
    (h
      : GraphQL.Execution.executeCollectedFields schema resolvers variables fuel
          parentType source left
        = .ok (data, 0))
    : ∃ data',
        GraphQL.Execution.executeCollectedFields schema resolvers variables fuel
            parentType source right
          = .ok (data', 0)
        ∧ (fields path data).Perm (fields path data') := by
  have hs := (basicFields_success_iff schema resolvers variables fuel parentType source left).mp
    ⟨data, h⟩
  obtain ⟨data', hd'⟩ :=
    (basicFields_success_iff schema resolvers variables fuel parentType source right).mpr
      (fun g hg => hs g (hp.mem_iff.mpr hg))
  refine ⟨data', hd', ?_⟩
  rw [basicFields_entries schema resolvers variables fuel parentType source path left data h,
    basicFields_entries schema resolvers variables fuel parentType source path right data' hd']
  exact hp.flatMap_right _

/-- Two successful basic field partitions concatenate successfully, by field-list
induction. -/
theorem basicFields_append (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues) (fuel : Nat) (parentType : Name)
    (source : ResolverValue ObjectRef)
    (left right : List (Name × List GraphQL.Execution.ExecutableField))
    (ld rd : List (Name × ResponseValue))
    (hl
      : GraphQL.Execution.executeCollectedFields schema resolvers variables fuel
          parentType source left
        = .ok (ld, 0))
    (hr
      : GraphQL.Execution.executeCollectedFields schema resolvers variables fuel
          parentType source right
        = .ok (rd, 0))
    : GraphQL.Execution.executeCollectedFields schema resolvers variables fuel parentType
        source (left ++ right)
      = .ok (ld ++ rd, 0) := by
  induction left generalizing ld with
  | nil =>
      simp [GraphQL.Execution.executeCollectedFields] at hl
      subst ld
      simpa using hr
  | cons group rest ih =>
      rcases group with ⟨name, selected⟩
      have hs := (basicFields_success_iff schema resolvers variables fuel parentType source
        ((name, selected) :: rest)).mp ⟨ld, hl⟩
      obtain ⟨head, hh⟩ := hs (name, selected) (by simp)
      obtain ⟨tail, ht⟩ :=
        (basicFields_success_iff schema resolvers variables fuel parentType source rest).mpr
          (fun g hg => hs g (by simp [hg]))
      simp only [GraphQL.Execution.executeCollectedFields, hh, ht,
        GraphQL.Execution.Result.combine, Nat.zero_add, Except.ok.injEq,
        Prod.mk.injEq, and_true] at hl
      subst ld
      simp [GraphQL.Execution.executeCollectedFields, hh, ih tail ht,
        GraphQL.Execution.Result.combine, List.append_assoc]

end GraphQL.IncrementalDelivery.Correctness.TypedResponse
