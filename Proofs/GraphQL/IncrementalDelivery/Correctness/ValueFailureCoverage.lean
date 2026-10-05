import Proofs.GraphQL.IncrementalDelivery.Correctness.EntryFailureCoverage
import Proofs.GraphQL.IncrementalDelivery.Correctness.InitialFailurePreservation
import Proofs.GraphQL.IncrementalDelivery.Correctness.OrdinaryFailureReflection

/-! Local mixed value coverage for nullable reference positions and outer-value guards. -/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution
open Semantics

-----------------------------------------------------------------------------------------
-- Nonbubbling ordinary values keep an initial value available for recursive comparison
-----------------------------------------------------------------------------------------

/-- Any ordinary successful mixed value has a successful initial value.
Witness: the general forward bubbling theorem; deferred/streamed data and error counts
may still differ. No queue or observation hypothesis is used.
-/
theorem completeValue_initialSuccess_of_ordinarySuccess (schema : Schema)
    (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
    (fieldType : TypeRef) (selected : List FieldDetails)
    (resolved : ResolverValue ObjectRef)
    (valid : ∀ field ∈ selected, ArgumentValidity.FieldArgumentsValid variables field)
    (path : ResponsePath) (usages : WorkQueueSemantics.NodeRefs) (deferMap : DeferMap)
    (allowStream : Bool) (state : NodeRef) (data : ResponseValue) (errors : Nat)
    (success
      : GraphQL.Execution.completeValue schema resolvers variables fuel fieldType
          (selected.map eraseField) resolved
        = .ok (data, errors))
    : ∃ initial count,
        ((completeValue schema resolvers variables fuel fieldType selected resolved path
            usages deferMap allowStream).run
          state).1.result
        = .ok (initial, count) :=
  (InitialFailures.completeValue_preserves_failures schema resolvers variables fuel
    fieldType selected resolved valid path usages deferMap allowStream
    state).1.initial_success
    data errors success

/-- An ordinary non-null mixed value cannot have an initially null or bubbling value.
Witness: forward value-failure preservation. This justifies descending into initial
objects/lists without assuming full successful reconstruction or zero counted errors.
-/
theorem completeValue_initialNonNull_of_ordinaryNonNull (schema : Schema)
    (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
    (fieldType : TypeRef) (selected : List FieldDetails)
    (resolved : ResolverValue ObjectRef)
    (valid : ∀ field ∈ selected, ArgumentValidity.FieldArgumentsValid variables field)
    (path : ResponsePath) (usages : WorkQueueSemantics.NodeRefs) (deferMap : DeferMap)
    (allowStream : Bool) (state : NodeRef) (data : ResponseValue) (errors : Nat)
    (success
      : GraphQL.Execution.completeValue schema resolvers variables fuel fieldType
          (selected.map eraseField) resolved
        = .ok (data, errors))
    (notNull : data ≠ .null)
    : ∃ initial count,
        ((completeValue schema resolvers variables fuel fieldType selected resolved path
            usages deferMap allowStream).run
            state).1.result
          = .ok (initial, count)
        ∧ initial ≠ .null :=
  (InitialFailures.completeValue_preserves_failures schema resolvers variables fuel
    fieldType selected resolved valid path usages deferMap allowStream
    state).initial_nonNull
    data errors success notNull

-----------------------------------------------------------------------------------------
-- Ordinary nullable nulls are available initially or explained by retained work
-----------------------------------------------------------------------------------------

/-- An ordinary null position has actual local initial-data or failed-task coverage.
Witness: the forward/reverse mixed failure pair at the actual value-completion state.
The typed null tag retains the ancestor-bubbling explanation under later field assembly.
The container flag and extra available positions are arbitrary.
-/
theorem completeValue_nullEntry_covered (schema : Schema)
    (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
    (fieldType : TypeRef) (selected : List FieldDetails)
    (resolved : ResolverValue ObjectRef)
    (valid : ∀ field ∈ selected, ArgumentValidity.FieldArgumentsValid variables field)
    (path : ResponsePath) (usages : WorkQueueSemantics.NodeRefs) (deferMap : DeferMap)
    (allowStream : Bool) (state : NodeRef) (errors : Nat)
    (isNull
      : GraphQL.Execution.completeValue schema resolvers variables fuel fieldType
          (selected.map eraseField) resolved
        = .ok (.null, errors))
    (containers : Bool) (extra : List ResponsePath)
    : let completed :=
        ((completeValue schema resolvers variables fuel fieldType selected
            resolved path usages deferMap allowStream).run
          state).1
      EntryExplained
        (DeliveryPaths.result (ResponsePositions.value containers path) completed.result
          ++ extra)
        completed.work (path, .null) := by
  exact nullEntry_explained
    (InitialFailures.completeValue_preserves_failures schema resolvers variables fuel fieldType
      selected resolved valid path usages deferMap allowStream state).1
    (OrdinaryFailures.completeValue_explains_failures schema resolvers variables fuel fieldType
      selected resolved valid path usages deferMap allowStream state)
    errors isNull containers extra

/-- All entries of an ordinary null value have local prepared completion coverage.
Witness: the single typed null entry and the general null-reflection theorem; the extra
inventory is precisely the completion's actual payload-seeded future positions.
-/
theorem completeValue_nullEntries_covered (schema : Schema)
    (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
    (fieldType : TypeRef) (selected : List FieldDetails)
    (resolved : ResolverValue ObjectRef)
    (valid : ∀ field ∈ selected, ArgumentValidity.FieldArgumentsValid variables field)
    (path : ResponsePath) (usages : WorkQueueSemantics.NodeRefs) (deferMap : DeferMap)
    (allowStream : Bool) (state : NodeRef) (errors : Nat)
    (isNull
      : GraphQL.Execution.completeValue schema resolvers variables fuel fieldType
          (selected.map eraseField) resolved
        = .ok (.null, errors))
    (containers : Bool)
    : let completed :=
        ((completeValue schema resolvers variables fuel fieldType selected
            resolved path usages deferMap allowStream).run
          state).1
      EntriesCovered containers (TypedResponse.value path .null)
        (DeliveryPaths.result (ResponsePositions.value containers path) completed.result
          ++ (sourceTasks [] none
                (Semantics.MixedPaths.resultCursors
                  (ResponsePositions.listCursors path) completed.result)
                completed.work).flatMap
              (SourceTask.positions containers)) completed.work := by
  dsimp only
  intro entry member _
  obtain rfl := List.mem_singleton.mp member
  exact completeValue_nullEntry_covered schema resolvers variables fuel fieldType selected
    resolved valid path usages deferMap allowStream state errors isNull containers _

end GraphQL.IncrementalDelivery.Correctness
