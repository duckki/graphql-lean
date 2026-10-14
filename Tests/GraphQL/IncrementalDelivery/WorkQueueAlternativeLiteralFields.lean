import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.ScheduledLiteralFields
import Tests.GraphQL.IncrementalDelivery.Execution

/-! Actual field-scope consumers construct recursive child relations from resolver
successes. The fatal scope retains prior nullable counts and skips a later stream key;
the healthy scope preserves that stream Work and final supply. No public changes. -/

namespace AlternativeLiteralFieldChecks

open GraphQL.IncrementalDelivery
open Execution AlternativeWorkQueue.NativeRefinement
open ScheduledErrors ScheduledWork

private def values : List (ResolverValue Nat) :=
  [.list [.null, .null], .list [.null, .null]]

private theorem matrix_values_literal : LiteralValue (.list values) := by
  apply LiteralValue.list
  intro value member
  simp [values] at member
  subst value
  apply LiteralValue.list
  intro value member
  simp at member
  subst value
  exact .null

private def resolvers : Resolvers Nat :=
  {
    Tests.resolvers with
      resolve :=
        fun parent field arguments source =>
          if field == "matrix" then
            some (.list values)
          else
            Tests.resolvers.resolve parent field arguments source
      resolve_argumentsEquivalent := by
        intro parent field first second source equivalent
        split
        · rfl
        · exact Tests.resolvers.resolve_argumentsEquivalent parent field first second source
            equivalent
  }

private def schema : GraphQL.Schema :=
  {
    Tests.schema with
      types :=
        .object
          {
            name := "LiteralQuery",
            fields :=
              [
                {
                  name := "matrix",
                  outputType := .list (.list (.nonNull (.named "String")))
                },
                { name := "required", outputType := .nonNull (.named "String") },
                { name := "values", outputType := .list (.named "String") }
              ]
          }
        :: Tests.schema.types
  }

private def source : ResolverValue Nat := .object "LiteralQuery" 0

private def matrixField : FieldDetails :=
  { fieldName := "matrix", arguments := [], selectionSet := [] }

private def requiredField : FieldDetails :=
  { fieldName := "required", arguments := [], selectionSet := [] }

private def streamField : FieldDetails :=
  { fieldName := "values", arguments := [], selectionSet := [], directives := [.stream] }

private theorem matrix_literal
    : LiteralFieldValues resolvers "LiteralQuery" source [matrixField] := by
  intro field member arguments value resolved
  simp only [List.mem_singleton] at member
  subst field
  change some (.list values) = some value at resolved
  cases resolved
  exact matrix_values_literal

private theorem required_literal
    : LiteralFieldValues resolvers "LiteralQuery" source [requiredField] := by
  intro field member arguments value resolved
  simp only [List.mem_singleton] at member
  subst field
  change none = some value at resolved
  cases resolved

private theorem stream_literal
    : LiteralFieldValues resolvers "LiteralQuery" source [streamField] := by
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

private def fatalFields : CollectedFieldsMap :=
  [("matrix", [matrixField]), ("required", [requiredField]), ("values", [streamField])]

private def healthyFields : CollectedFieldsMap :=
  [("matrix", [matrixField]), ("values", [streamField])]

private theorem fatal_fields_literal
    : LiteralFields resolvers "LiteralQuery" source fatalFields := by
  intro entry member
  simp only [fatalFields, List.mem_cons, List.not_mem_nil, or_false] at member
  obtain rfl | rfl | rfl := member
  · exact matrix_literal
  · exact required_literal
  · exact stream_literal

private theorem healthy_fields_literal
    : LiteralFields resolvers "LiteralQuery" source healthyFields := by
  intro entry member
  simp only [healthyFields, List.mem_cons, List.not_mem_nil, or_false] at member
  obtain rfl | rfl := member
  · exact matrix_literal
  · exact stream_literal

private def run (cancel : Bool) (fields : CollectedFieldsMap) (supply : Nat) :=
  let execute :=
    if cancel then
      @ScheduledExecution.executeCollectedFields Nat
    else
      @Execution.executeCollectedFields Nat
  (execute schema resolvers [] 7 "LiteralQuery" source fields [] [] []).run supply

private theorem fatal_scope_refines (supply : Nat)
    : CompletionRefines id (run true fatalFields supply).1
        (run false fatalFields supply).1 :=
  (literalFieldScopeRefinement_holds _ schema resolvers [] 7 "LiteralQuery" source
    fatalFields [] [] [] supply fatal_fields_literal).1

private theorem healthy_scope_refines (supply : Nat)
    : CompletionRefines id (run true healthyFields supply).1
        (run false healthyFields supply).1
      ∧ (run true healthyFields supply).2 = (run false healthyFields supply).2 := by
  obtain ⟨related, supplySame⟩ :=
    literalFieldScopeRefinement_holds _ schema resolvers [] 7 "LiteralQuery" source
      healthyFields [] [] [] supply healthy_fields_literal
  exact ⟨related, supplySame (by cbv)⟩

-- The first field's completed nullable counts remain, then the fatal field cuts the scope.
-- The untouched streamed field contributes no error but allocates a key only in eager.
example : (run true fatalFields 17).1.result = .error 3 := by cbv
example : (run false fatalFields 17).1.result = .error 5 := by cbv
example : (run true fatalFields 17).2 = 17 := by cbv
example : (run false fatalFields 17).2 = 18 := by cbv

-- No outer fatal cut: initial counts differ, but full retained stream Work is related.
example : countedErrors (run true healthyFields 17).1.result = 2 := by cbv
example : countedErrors (run false healthyFields 17).1.result = 4 := by cbv
example : (run true healthyFields 17).2 = 18 := by cbv
example : (run false healthyFields 17).2 = 18 := by cbv

example : SiblingWorkRefinement := siblingWorkRefinement_holds
example : LiteralFieldScopeRefinement := literalFieldScopeRefinement_holds

#print axioms siblingWorkRefinement_holds
#print axioms executeCollectedFields_work_refines_of_children
#print axioms completeListValue_work_refines_of_children
#print axioms literalFieldScopeRefinement_holds
#print axioms literal_fieldActions_paired
#print axioms fatal_scope_refines
#print axioms healthy_scope_refines

end AlternativeLiteralFieldChecks
