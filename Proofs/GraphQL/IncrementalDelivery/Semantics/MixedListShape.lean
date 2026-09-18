import Proofs.GraphQL.IncrementalDelivery.Semantics.Collection

/-! List completion preserves the number of initial items on success, even when
those items generate nested defer/stream work. An active stream therefore starts
at the length of its actual initial list payload, not an unrelated ghost offset.
-/

namespace GraphQL.IncrementalDelivery.Semantics.MixedPaths

open GraphQL.IncrementalDelivery.Execution

attribute [local simp] id_pure_eq id_bind_eq id_map_eq run_bind run_map

theorem completeListValue_result_length (schema : Schema)
    (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
    (itemType : TypeRef) (selected : List ExecutableField)
    (values : List (ResolverValue ObjectRef)) (path : ResponsePath) (index : Nat)
    (usages : List Nat) (deferMap : DeferMap) (state : Nat)
    (data : List ResponseValue) (errors : Nat)
    (h
      : ((completeListValue schema resolvers variables fuel itemType selected values
            path index usages deferMap).run
          state).1.result
        = .ok (data, errors))
    : data.length = values.length := by
  induction values generalizing index state data errors with
  | nil =>
      simp only [completeListValue, StateT.run_pure, id_pure_eq, Completion.pure,
        Except.ok.injEq, Prod.mk.injEq] at h
      simp [← h.1]
  | cons value rest ih =>
      let head := (completeValue schema resolvers variables fuel itemType selected value
        (path ++ [.index index]) usages deferMap false).run state
      let tail := (completeListValue schema resolvers variables fuel itemType selected rest
        path (index + 1) usages deferMap).run head.2
      simp only [completeListValue, run_bind, StateT.run_pure, id_pure_eq] at h
      change (Completion.combine List.cons head.1 tail.1).result = .ok (data, errors) at h
      cases hh : head.1.result with
      | error count =>
          cases ht : tail.1.result <;>
            simp [Completion.combine, hh, ht, GraphQL.Execution.Result.combine,
              Completion.error] at h
      | ok pair =>
          rcases pair with ⟨item, itemErrors⟩
          cases ht : tail.1.result with
          | error count =>
              simp [Completion.combine, hh, ht, GraphQL.Execution.Result.combine,
                Completion.error] at h
          | ok pair =>
              rcases pair with ⟨items, itemErrors⟩
              have hl := ih (index + 1) head.2 items itemErrors ht
              simp only [Completion.combine, hh, ht, GraphQL.Execution.Result.combine,
                Except.ok.injEq, Prod.mk.injEq] at h
              rw [← h.1]
              simp only [List.length_cons, hl]

theorem activeStream_prefix_length (schema : Schema)
    (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
    (itemType : TypeRef) (selected : List ExecutableField)
    (values : List (ResolverValue ObjectRef)) (path : ResponsePath)
    (usages : List Nat) (deferMap : DeferMap) (state count : Nat)
    (data : List ResponseValue) (errors : Nat)
    (h
      : ((completeListValue schema resolvers variables fuel itemType selected
            (values.take count) path 0 usages deferMap).run
          state).1.result
        = .ok (data, errors))
    (ht : (values.drop count).isEmpty = false)
    : data.length = count := by
  have hl := completeListValue_result_length schema resolvers variables fuel itemType
    selected (values.take count) path 0 usages deferMap state data errors h
  have hn : count < values.length := by
    by_cases hshort : values.length ≤ count
    · have he : values.drop count = [] := List.drop_eq_nil_iff.mpr hshort
      simp [he] at ht
    · omega
  simpa only [List.length_take, Nat.min_eq_left (Nat.le_of_lt hn)] using hl

end GraphQL.IncrementalDelivery.Semantics.MixedPaths
