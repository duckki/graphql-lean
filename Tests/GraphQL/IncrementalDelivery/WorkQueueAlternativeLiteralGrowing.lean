import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.LiteralGrowingFields
import Tests.GraphQL.IncrementalDelivery.Execution

/-! Actual literal field-scope construction after a pre-existing allocation gap.
A fatal scope keeps its prior nullable error, skips a stream, and extends the same map;
a healthy scope retains the mapped stream and both inherited defer/ancestor images. -/

namespace AlternativeLiteralGrowingChecks

open GraphQL.IncrementalDelivery
open Execution AlternativeWorkQueue.NativeRefinement
open KeyRenaming ScheduledErrors ScheduledWork

private def details (name : GraphQL.Name) : FieldDetails :=
  {
    fieldName := name,
    arguments := [],
    selectionSet := [],
    directives := if name == "values" then [.stream] else [],
    deferUsage := some { ref := 17, ancestors := [16] }
  }

private def fatalFields : CollectedFieldsMap :=
  [
    ("nullable", [details "fail"]),
    ("first", [details "required"]),
    ("second", [details "required"]),
    ("skipped", [details "values"])
  ]

private def healthyFields : CollectedFieldsMap :=
  [("nullable", [details "fail"]), ("retained", [details "values"])]

private def context : DeferMap :=
  [{ node := { ref := 17, path := [] }, ancestors := [{ ref := 16, path := [] }] }]

private def keys : Nat → Nat := retargetTail id 18 21

private theorem initial : SupplyMap keys 20 23 := by
  have prefixBound : PrefixBelow id 18 21 := by intro key earlier; dsimp; omega
  refine ⟨retargetTail_injective (fun _ _ same => same) prefixBound, ?_, ?_, ?_⟩
  · intro key earlier
    unfold keys retargetTail
    split
    · change key < 23
      omega
    · omega
  · cbv
  · exact (retargetTail_fresh id 18 21).advance (by omega)

private theorem failed_literal (name : GraphQL.Name)
    (failed : name = "fail" ∨ name = "required")
    : LiteralFieldValues Tests.resolvers "Query" (.object "Query" 0) [details name] := by
  intro field member arguments value resolved
  simp only [List.mem_singleton] at member
  subst field
  rcases failed with rfl | rfl
  all_goals change none = some value at resolved
  all_goals cases resolved

private theorem values_literal
    : LiteralFieldValues Tests.resolvers "Query" (.object "Query" 0)
        [details "values"] := by
  intro field member arguments value resolved
  simp only [List.mem_singleton] at member
  subst field
  change some (.list [.scalar "x", .null, .scalar "z"]) = some value at resolved
  cases resolved
  apply LiteralValue.list
  intro value member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  obtain rfl | rfl | rfl := member
  · exact .scalar _
  · exact .null
  · exact .scalar _

private theorem fatal_literal
    : LiteralFields Tests.resolvers "Query" (.object "Query" 0) fatalFields := by
  intro entry member
  simp only [fatalFields, List.mem_cons, List.not_mem_nil, or_false] at member
  obtain rfl | rfl | rfl | rfl := member
  · exact failed_literal _ (.inl rfl)
  · exact failed_literal _ (.inr rfl)
  · exact failed_literal _ (.inr rfl)
  · exact values_literal

private theorem healthy_literal
    : LiteralFields Tests.resolvers "Query" (.object "Query" 0) healthyFields := by
  intro entry member
  simp only [healthyFields, List.mem_cons, List.not_mem_nil, or_false] at member
  obtain rfl | rfl := member
  · exact failed_literal _ (.inl rfl)
  · exact values_literal

private def cut (fields : CollectedFieldsMap) :=
  (ScheduledExecution.executeCollectedFields Tests.schema Tests.resolvers [] 7 "Query"
    (.object "Query" 0) fields [] [17] context).run
    20

private def eager (fields : CollectedFieldsMap) :=
  (Execution.executeCollectedFields Tests.schema Tests.resolvers [] 7 "Query"
    (.object "Query" 0) (KeyRenaming.fields keys fields) [] ([17].map keys)
    (context.map (fragment keys))).run
    23

private theorem constructed (fields : CollectedFieldsMap)
    (literal : LiteralFields Tests.resolvers "Query" (.object "Query" 0) fields)
    (bounded : ∀ entry ∈ fields, ∀ field ∈ entry.2, ∀ key ∈ fieldKeys field, key < 20)
    : ∃ next, RunRefines keys next 20 23 (cut fields) (eager fields) := by
  exact literalGrowingFieldScope_holds _ Tests.schema Tests.resolvers [] 7 "Query"
    (.object "Query" 0) fields [] [17] context keys 20 23 literal initial bounded
    (by simp)
    (by simp [context, GraphQL.IncrementalDelivery.Semantics.RefRoles.fragmentRefs])

private theorem fatal_constructed
    : ∃ next, RunRefines keys next 20 23 (cut fatalFields) (eager fatalFields) := by
  apply constructed _ fatal_literal
  intro entry member field inFields key inKeys
  simp only [fatalFields, List.mem_cons, List.not_mem_nil, or_false] at member
  obtain rfl | rfl | rfl | rfl := member
  all_goals simp only [List.mem_singleton] at inFields
  all_goals subst field
  all_goals simp [fieldKeys, details] at inKeys
  all_goals omega

private theorem healthy_constructed
    : ∃ next, RunRefines keys next 20 23 (cut healthyFields) (eager healthyFields) := by
  apply constructed _ healthy_literal
  intro entry member field inFields key inKeys
  simp only [healthyFields, List.mem_cons, List.not_mem_nil, or_false] at member
  obtain rfl | rfl := member
  all_goals simp only [List.mem_singleton] at inFields
  all_goals subst field
  all_goals simp [fieldKeys, details] at inKeys
  all_goals omega

-- Recorded nullable failure is retained. Only the untouched suffix's execution is cut.
example : (cut fatalFields).1.result = .error 2 := by cbv
example : (eager fatalFields).1.result = .error 3 := by cbv
example : (cut fatalFields).2 = 20 ∧ (eager fatalFields).2 = 24 := by cbv

example
    : ∃ next,
        next 16 = 16
        ∧ next 17 = 17
        ∧ next 20 = 24
        ∧ CompletionRefines next (cut fatalFields).1 (eager fatalFields).1 := by
  obtain ⟨next, related⟩ := fatal_constructed
  refine ⟨next, ?_, ?_, ?_, related.completion⟩
  · exact (related.compatible 16 (by omega)).trans (by cbv)
  · exact (related.compatible 17 (by omega)).trans (by cbv)
  · simpa only [show (cut fatalFields).2 = 20 by cbv,
      show (eager fatalFields).2 = 24 by cbv] using related.supplies.boundary

example : (cut healthyFields).2 = 21 ∧ (eager healthyFields).2 = 24 := by cbv

example
    : ∃ next,
        next 16 = 16
        ∧ next 17 = 17
        ∧ next 21 = 24
        ∧ CompletionRefines next (cut healthyFields).1 (eager healthyFields).1 := by
  obtain ⟨next, related⟩ := healthy_constructed
  refine ⟨next, ?_, ?_, ?_, related.completion⟩
  · exact (related.compatible 16 (by omega)).trans (by cbv)
  · exact (related.compatible 17 (by omega)).trans (by cbv)
  · simpa only [show (cut healthyFields).2 = 21 by cbv,
      show (eager healthyFields).2 = 24 by cbv] using related.supplies.boundary

example : LiteralGrowingFieldScope := literalGrowingFieldScope_holds

#print axioms literalGrowingFieldScope_holds
#print axioms literal_responseField_run
#print axioms literal_value_maps
#print axioms fatal_constructed
#print axioms healthy_constructed

end AlternativeLiteralGrowingChecks
