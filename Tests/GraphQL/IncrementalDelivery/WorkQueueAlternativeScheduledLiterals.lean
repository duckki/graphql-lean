import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.ScheduledLiteralRefinement
import Tests.GraphQL.IncrementalDelivery.Execution

/-! Recursive literal-fragment roots applied to actual completion/stream runs. Counts
remain observable; the witnesses are constructed by the general theorem, not by assuming
paired child actions or output Work correspondence. Object execution remains excluded. -/

namespace AlternativeScheduledLiteralChecks

open GraphQL.IncrementalDelivery
open Execution AlternativeWorkQueue.NativeRefinement
open ScheduledErrors ScheduledWork

-- Exact root types, including arbitrary metadata, supplies, fuel and stream permission.
example : LiteralNoStreamRefinement := literalNoStreamRefinement_holds
example : LiteralCompletionRefinement := literalCompletionRefinement_holds

example (schema : GraphQL.Schema) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues) (fuel : Nat) (fieldType : GraphQL.TypeRef)
    (fields : List FieldDetails) (value : ResolverValue ObjectRef) (path : ResponsePath)
    (usages : List Nat) (context : DeferMap) (allowStream : Bool)
    (literal : LiteralValue value) (supply : Nat)
    : CompletionRefines id
        ((ScheduledExecution.completeValue schema resolvers variables fuel fieldType
            fields value path usages context allowStream).run
          supply).1
        ((Execution.completeValue schema resolvers variables fuel fieldType fields value
            path usages context allowStream).run
          supply).1
      ∧ ((ScheduledExecution.completeValue schema resolvers variables fuel fieldType
            fields value path usages context allowStream).run
          supply).2
        = ((Execution.completeValue schema resolvers variables fuel fieldType fields value
              path usages context allowStream).run
            supply).2 :=
  literalCompletionRefinement_holds _ schema resolvers variables fuel fieldType fields
    value path usages context allowStream literal supply

private def values : List (ResolverValue Nat) :=
  [.list [.null, .null], .list [.null, .null]]

private theorem values_literal : ∀ value ∈ values, LiteralValue value := by
  intro value member
  simp [values] at member
  subst value
  apply LiteralValue.list
  intro value member
  simp at member
  subst value
  exact .null

private def nullableItem : GraphQL.TypeRef := .list (.nonNull (.named "String"))

private def streamField (count : Nat) : FieldDetails :=
  {
    fieldName := "matrix",
    arguments := [],
    selectionSet := [],
    directives := [.stream (.boolean true) none (.int count)]
  }

private def run (cancel stream strict : Bool) (count : Nat) (supply : Nat) :=
  let complete :=
    if cancel then @ScheduledExecution.completeValue Nat else @Execution.completeValue Nat
  let itemType := if strict then .nonNull nullableItem else nullableItem
  (complete Tests.schema Tests.resolvers [] 6 (.list itemType) [streamField count]
    (.list values) [] [] [] stream).run
    supply

private theorem runs_refine (stream strict : Bool) (count supply : Nat)
    : CompletionRefines id (run true stream strict count supply).1
        (run false stream strict count supply).1
      ∧ (run true stream strict count supply).2
        = (run false stream strict count supply).2 :=
  literalCompletionRefinement_holds _ Tests.schema Tests.resolvers [] 6 _
    [streamField count] (.list values) [] [] [] stream (.list values_literal) supply

-- Inner field-free list cuts and the outer non-null item cut compound: 4 eager / 1 cut.
example : (run false false true 0 23).1.result = .ok (.null, 4) := by cbv
example : (run true false true 0 23).1.result = .ok (.null, 1) := by cbv
example : (run true false true 0 23).2 = 23 := by cbv
example : (run false false true 0 23).2 = 23 := by cbv

-- Nullable items both finish: their already completed counts are accumulated, not clamped.
example : (run false false false 0 23).1.result = .ok (.list [.null, .null], 4) := by cbv
example : (run true false false 0 23).1.result = .ok (.list [.null, .null], 2) := by cbv

private def itemCounts : Work → List Nat
  | .empty | .executionGroup _ _ _ _ => []
  | .combine left right => itemCounts left ++ itemCounts right
  | .stream _ items => items.map (fun item => countedErrors item.1)

-- Initial zero counted errors do not mean the retained stream payloads are error-free.
example : (run true true false 0 23).1.result = .ok (.list [], 0) := by cbv
example : itemCounts (run true true false 0 23).1.work = [1, 1] := by cbv
example : itemCounts (run false true false 0 23).1.work = [2, 2] := by cbv
example : (run true true false 0 23).2 = 24 := by cbv
example : (run false true false 0 23).2 = 24 := by cbv

-- Both stream policies stop at the first fatal item, with related recursive counts.
example : itemCounts (run true true true 0 23).1.work = [1] := by cbv
example : itemCounts (run false true true 0 23).1.work = [2] := by cbv

-- A fatal initial item never creates the outer stream descriptor in either policy.
example : (run true true true 1 23).2 = 23 := by cbv
example : (run false true true 1 23).2 = 23 := by cbv

example
    : CompletionRefines id (run true true false 0 23).1 (run false true false 0 23).1 :=
  (runs_refine true false 0 23).1

-- The domain is necessary: resolver-owned objects may collect/allocate deferred work.
example (ref : Nat)
    : ¬LiteralValue (GraphQL.Execution.ResolverValue.object "User" ref) := by
  intro literal
  cases literal

#print axioms literalNoStreamRefinement_holds
#print axioms literalCompletionRefinement_holds
#print axioms literal_completeStreamItems_refines
#print axioms literal_completeListValueWithStream_refines
#print axioms CompletionRefines.fatal_cut
#print axioms runs_refine

end AlternativeScheduledLiteralChecks
