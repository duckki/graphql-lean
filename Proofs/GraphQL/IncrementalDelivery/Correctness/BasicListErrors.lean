import Proofs.GraphQL.IncrementalDelivery.Correctness.SourceListReconstruction

/-! Ordinary list partitioning and bubbling with arbitrary counted errors. -/

namespace GraphQL.IncrementalDelivery.Correctness.SourceReconstruction
open GraphQL.IncrementalDelivery.Execution

/-- Splitting at a stream boundary preserves ordinary list completion, including errors.
Witness: take/drop recombine the original input, then exact partition combination applies.
No assumption about an exhausted suffix or the stream's first failing item is required.
-/
theorem basicList_split_result (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues) (fuel : Nat) (itemType : TypeRef)
    (selected : List GraphQL.Execution.ExecutableField)
    (values : List (ResolverValue ObjectRef)) (count : Nat)
    : GraphQL.Execution.completeValueList schema resolvers variables fuel itemType
        selected values
      = GraphQL.Execution.Result.combine List.append
          (GraphQL.Execution.completeValueList schema resolvers variables fuel itemType
            selected (values.take count))
          (GraphQL.Execution.completeValueList schema resolvers variables fuel itemType
            selected (values.drop count)) := by
  simpa only [List.take_append_drop]
    using Semantics.basicCompleteValueList_append schema resolvers variables
      fuel itemType selected (values.take count) (values.drop count)

/-- An ordinary list bubbles exactly when at least one completed item bubbles.
Witness: input-list induction and the result-combination cases. This locates an actual
failing item; nullable item errors that return null data do not themselves bubble the list.
-/
theorem basicList_bubbles_iff (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues) (fuel : Nat) (itemType : TypeRef)
    (selected : List GraphQL.Execution.ExecutableField)
    (values : List (ResolverValue ObjectRef))
    : (∃ errors,
        GraphQL.Execution.completeValueList schema resolvers variables fuel
          itemType selected values
        = .error errors)
      ↔ ∃ value ∈ values,
          ∃ errors,
            GraphQL.Execution.completeValue schema resolvers variables fuel itemType
              selected value
            = .error errors := by
  induction values with
  | nil => simp [GraphQL.Execution.completeValueList]
  | cons head tail ih =>
      simp only [List.mem_cons, or_and_right, exists_or, exists_eq_left]
      rw [← ih]
      cases left : GraphQL.Execution.completeValue schema resolvers variables fuel
          itemType selected head <;>
        cases right : GraphQL.Execution.completeValueList schema resolvers variables fuel
          itemType selected tail <;>
        simp [GraphQL.Execution.completeValueList, GraphQL.Execution.Result.combine, left, right]

-----------------------------------------------------------------------------------------
-- Stream success retains nullable errors, and stream failure matches ordinary bubbling
-----------------------------------------------------------------------------------------

/-- Successful retained stream results reconstruct ordinary items and all counted errors.
Witness: input-list induction; each successful item contributes its data and error count.
Positive nullable-item errors are retained rather than mistaken for stream failure.
-/
theorem basicStreamResults_success_withErrors (schema : Schema)
    (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
    (itemType : TypeRef) (fields : List FieldDetails)
    (values : List (ResolverValue ObjectRef)) (entries : List (ResponseValue × Nat))
    (successful
      : Semantics.basicStreamResults schema resolvers variables fuel itemType fields
          values
        = entries.map Except.ok)
    : GraphQL.Execution.completeValueList schema resolvers variables fuel itemType
        (fields.map Semantics.eraseField) values
      = .ok (entries.map Prod.fst, (entries.map Prod.snd).sum) := by
  induction values generalizing entries with
  | nil =>
      cases entries <;>
        simp_all [Semantics.basicStreamResults, GraphQL.Execution.completeValueList]
  | cons value rest ih =>
      cases headCompleted
            : GraphQL.Execution.completeValue schema resolvers variables fuel
                itemType (fields.map Semantics.eraseField) value with
      | error errors => cases entries <;> simp_all [Semantics.basicStreamResults]
      | ok pair =>
          cases entries with
          | nil => simp [Semantics.basicStreamResults, headCompleted] at successful
          | cons entry entries =>
              simp only [Semantics.basicStreamResults, headCompleted, List.map_cons,
                List.cons.injEq, Except.ok.injEq] at successful
              obtain ⟨rfl, tailSuccessful⟩ := successful
              simp [GraphQL.Execution.completeValueList, headCompleted,
                ih entries tailSuccessful, GraphQL.Execution.Result.combine]

/-- Ordinary list success supplies all retained stream values with their counted errors.
Witness: successful list combination forces both item and suffix success; list induction
collects the exact item data and error total without requiring zero errors.
-/
theorem basicList_success_streamResults (schema : Schema)
    (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
    (itemType : TypeRef) (fields : List FieldDetails)
    (values : List (ResolverValue ObjectRef)) {data errors}
    (successful
      : GraphQL.Execution.completeValueList schema resolvers variables fuel itemType
          (fields.map Semantics.eraseField) values
        = .ok (data, errors))
    : ∃ entries : List (ResponseValue × Nat),
        Semantics.basicStreamResults schema resolvers variables fuel itemType fields
            values
          = entries.map Except.ok
        ∧ entries.map Prod.fst = data
        ∧ (entries.map Prod.snd).sum = errors := by
  induction values generalizing data errors with
  | nil =>
      simp only [GraphQL.Execution.completeValueList, Except.ok.injEq, Prod.mk.injEq]
        at successful
      obtain ⟨rfl, rfl⟩ := successful
      exact ⟨[], rfl, rfl, rfl⟩
  | cons value rest ih =>
      cases headCompleted : GraphQL.Execution.completeValue schema resolvers variables fuel
          itemType (fields.map Semantics.eraseField) value <;>
        cases tailCompleted : GraphQL.Execution.completeValueList schema resolvers variables
          fuel itemType (fields.map Semantics.eraseField) rest <;>
        simp only [GraphQL.Execution.completeValueList, headCompleted, tailCompleted,
          GraphQL.Execution.Result.combine, Except.ok.injEq, Prod.mk.injEq,
          reduceCtorEq] at successful
      rename_i headPair tailPair
      obtain ⟨rfl, rfl⟩ := successful
      obtain ⟨entries, outcomes, sameData, sameErrors⟩ := ih tailCompleted
      exact ⟨
        headPair :: entries,
        by simp [Semantics.basicStreamResults, headCompleted, outcomes],
        by simp [sameData],
        by simp [sameErrors]
      ⟩

/-- The short-circuit source retains a failure exactly when ordinary list completion
bubbles. Witness: input-list induction follows the first failed item; ordinary completion
may still count later failures, so only existence, not equality of totals, is asserted.
-/
theorem basicStreamResults_failure_iff_bubbles (schema : Schema)
    (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
    (itemType : TypeRef) (fields : List FieldDetails)
    (values : List (ResolverValue ObjectRef))
    : (∃ errors,
        (.error errors : Result ResponseValue)
        ∈ Semantics.basicStreamResults schema resolvers variables fuel itemType fields
            values)
      ↔ ∃ errors,
          GraphQL.Execution.completeValueList schema resolvers variables fuel itemType
            (fields.map Semantics.eraseField) values
          = .error errors := by
  induction values with
  | nil => simp [Semantics.basicStreamResults, GraphQL.Execution.completeValueList]
  | cons value rest ih =>
      cases headCompleted : GraphQL.Execution.completeValue schema resolvers variables fuel
          itemType (fields.map Semantics.eraseField) value <;>
        cases tailCompleted : GraphQL.Execution.completeValueList schema resolvers variables
          fuel itemType (fields.map Semantics.eraseField) rest <;>
        simp_all [Semantics.basicStreamResults, GraphQL.Execution.completeValueList,
          GraphQL.Execution.Result.combine]

/-- A failing short-circuit stream outcome identifies an actual input item with that
failure. Witness: input-list induction follows the retained prefix until its error.
The ordinary completion may count further errors; no equality of total counts is claimed.
-/
theorem basicStreamFailure_hasItem (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues) (fuel : Nat) (itemType : TypeRef)
    (fields : List FieldDetails) (values : List (ResolverValue ObjectRef)) {errors}
    (failed
      : (.error errors : Result ResponseValue)
        ∈ Semantics.basicStreamResults schema resolvers variables fuel itemType fields
            values)
    : ∃ value ∈ values,
        GraphQL.Execution.completeValue schema resolvers variables fuel itemType
          (fields.map Semantics.eraseField) value
        = .error errors := by
  induction values with
  | nil => simp [Semantics.basicStreamResults] at failed
  | cons head tail ih =>
      cases completed
            : GraphQL.Execution.completeValue schema resolvers variables fuel
                itemType (fields.map Semantics.eraseField) head with
      | error count =>
          simp [Semantics.basicStreamResults, completed] at failed
          exact ⟨head, by simp, by simpa only [failed] using completed⟩
      | ok pair =>
          simp [Semantics.basicStreamResults, completed] at failed
          obtain ⟨value, member, outcome⟩ := ih failed
          exact ⟨value, List.mem_cons_of_mem _ member, outcome⟩

/-- A retained failed plain stream item forces ordinary list bubbling.
Witness: item-context execution agrees with the short-circuit source outcomes; their
failure identifies a real item, and ordinary-list bubbling follows from that item.
Only item selections are plain: the outer streaming directive remains unrestricted.
-/
theorem completeStreamItems_itemContext_bubbles (schema : Schema)
    (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
    (itemType : TypeRef) (fields : List FieldDetails)
    (values : List (ResolverValue ObjectRef))
    (plain : Semantics.ItemFieldsInContext none fields) (path : ResponsePath)
    (index state errors : Nat) (children : Work)
    (failed
      : (.error errors, children)
        ∈ ((completeStreamItems schema resolvers variables fuel itemType fields values
              path index).run
            state).1)
    : ∃ count,
        GraphQL.Execution.completeValueList schema resolvers variables fuel itemType
          (fields.map Semantics.eraseField) values
        = .error count := by
  have mapped : (.error errors : Result ResponseValue)
      ∈ Semantics.basicStreamResults schema resolvers variables fuel itemType fields values := by
    rw [← (Semantics.completeStreamItems_itemContext schema resolvers variables fuel itemType
      fields values plain path index state).2.1]
    exact List.mem_map.mpr ⟨_, failed, rfl⟩
  obtain ⟨value, member, outcome⟩ := basicStreamFailure_hasItem schema resolvers variables fuel
    itemType fields values mapped
  exact (basicList_bubbles_iff schema resolvers variables fuel itemType
    (fields.map Semantics.eraseField) values).mpr ⟨value, member, errors, outcome⟩

/-- Ordinary bubbling is represented by an actual retained failed plain stream item.
Witness: short-circuit failure equivalence and the executable item-context projection.
Together with the reverse direction this prevents silently missing a failed stream tail.
-/
theorem completeStreamItems_itemContext_failure_iff (schema : Schema)
    (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
    (itemType : TypeRef) (fields : List FieldDetails)
    (values : List (ResolverValue ObjectRef))
    (plain : Semantics.ItemFieldsInContext none fields) (path : ResponsePath)
    (index state : Nat)
    : (∃ errors children,
        (.error errors, children)
        ∈ ((completeStreamItems schema resolvers variables fuel itemType fields values
              path index).run
            state).1)
      ↔ ∃ errors,
          GraphQL.Execution.completeValueList schema resolvers variables fuel itemType
            (fields.map Semantics.eraseField) values
          = .error errors := by
  constructor
  · rintro ⟨errors, children, failed⟩
    exact completeStreamItems_itemContext_bubbles schema resolvers variables fuel itemType
      fields values plain path index state errors children failed
  · intro bubbled
    obtain ⟨errors, retained⟩ := (basicStreamResults_failure_iff_bubbles schema resolvers
      variables fuel itemType fields values).mpr bubbled
    rw [← (Semantics.completeStreamItems_itemContext schema resolvers variables fuel itemType
      fields values plain path index state).2.1] at retained
    obtain ⟨⟨result, children⟩, member, same⟩ := List.mem_map.mp retained
    dsimp only at same
    subst result
    exact ⟨errors, children, member⟩

end GraphQL.IncrementalDelivery.Correctness.SourceReconstruction
