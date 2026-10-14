import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.EagerOriginErasure
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.RecursiveExecutionConstruction
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.OriginRefinement

/-! Reuse the constructed execution maps at actual annotated child boundaries.
Exact erasure supplies the same final supplies and metadata-prefix extension; it
does not infer origin coverage from a count bound. -/

namespace
  GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.OriginAccounting

open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Semantics
open ScheduledWork KeyRenaming

theorem value_mapped_run (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues) (fuel : Nat) (fieldType : TypeRef)
    (fields : List FieldDetails) (source : ResolverValue ObjectRef) (path : ResponsePath)
    (usages : List Nat) (context : DeferMap) (allowStream : Bool) (route : List Nat)
    (keys : Nat → Nat) (left right : Nat) (supplies : SupplyMap keys left right)
    (ordered : ∀ details ∈ fields, UsageBefore left details.deferUsage)
    (usageBound : ∀ key ∈ usages, key < left)
    (contextBound : ∀ key ∈ context.flatMap RefRoles.fragmentRefs, key < left)
    : ∃ next,
        RunRefines keys next left right
          (eraseCompletionRun
            ((RecordedExecution.completeValue schema resolvers variables fuel
                fieldType fields source path usages context allowStream route).run
              left))
          (eraseCompletionRun
            ((EagerRecordedExecution.completeValue schema resolvers variables fuel
                fieldType (fields.map (field keys)) source path (usages.map keys)
                (context.map (fragment keys)) allowStream route).run
              right)) := by
  simpa only [completeValue_erases, EagerErasure.completeValue_erases]
    using valueRunConstruction_holds schema resolvers variables fuel fieldType fields
      source path usages context allowStream keys left right supplies ordered usageBound
      contextBound

theorem field_mapped_run (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues) (fuel : Nat) (parentType : Name)
    (source : ResolverValue ObjectRef) (name : Name) (fields : List FieldDetails)
    (path : ResponsePath) (usages : List Nat) (context : DeferMap) (route : List Nat)
    (keys : Nat → Nat) (left right : Nat) (supplies : SupplyMap keys left right)
    (ordered : ∀ details ∈ fields, UsageBefore left details.deferUsage)
    (usageBound : ∀ key ∈ usages, key < left)
    (contextBound : ∀ key ∈ context.flatMap RefRoles.fragmentRefs, key < left)
    : ∃ next,
        RunRefines keys next left right
          (eraseCompletionRun
            ((RecordedExecution.executeResponseField schema resolvers variables fuel
                parentType source name fields path usages context route).run
              left))
          (eraseCompletionRun
            ((EagerRecordedExecution.executeResponseField schema resolvers variables fuel
                parentType source name (fields.map (field keys)) path (usages.map keys)
                (context.map (fragment keys)) route).run
              right)) := by
  simpa only [executeResponseField_erases, EagerErasure.executeResponseField_erases]
    using responseField_run_of_values schema resolvers variables fuel
      (valueRunConstruction_holds schema resolvers variables (fuel - 1)) parentType source
      name fields path usages context keys left right supplies ordered usageBound
      contextBound

theorem fields_mapped_run (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues) (fuel : Nat) (parentType : Name)
    (source : ResolverValue ObjectRef) (fields : CollectedFieldsMap)
    (path : ResponsePath) (usages : List Nat) (context : DeferMap) (route : List Nat)
    (keys : Nat → Nat) (left right : Nat) (supplies : SupplyMap keys left right)
    (ordered : FieldsBefore left fields) (usageBound : ∀ key ∈ usages, key < left)
    (contextBound : ∀ key ∈ context.flatMap RefRoles.fragmentRefs, key < left)
    : ∃ next,
        RunRefines keys next left right
          (eraseCompletionRun
            ((RecordedExecution.executeCollectedFields schema resolvers variables fuel
                parentType source fields path usages context route).run
              left))
          (eraseCompletionRun
            ((EagerRecordedExecution.executeCollectedFields schema resolvers variables
                fuel parentType source (KeyRenaming.fields keys fields) path
                (usages.map keys) (context.map (fragment keys)) route).run
              right)) := by
  simpa only [executeCollectedFields_erases, EagerErasure.executeCollectedFields_erases]
    using fieldScopeRunConstruction_holds schema resolvers variables fuel parentType
      source fields path usages context keys left right supplies ordered usageBound
      contextBound

theorem list_mapped_run (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues) (fuel : Nat) (itemType : TypeRef)
    (fields : List FieldDetails) (sources : List (ResolverValue ObjectRef))
    (path : ResponsePath) (index : Nat) (usages : List Nat) (context : DeferMap)
    (route : List Nat) (keys : Nat → Nat) (left right : Nat)
    (supplies : SupplyMap keys left right)
    (ordered : ∀ details ∈ fields, UsageBefore left details.deferUsage)
    (usageBound : ∀ key ∈ usages, key < left)
    (contextBound : ∀ key ∈ context.flatMap RefRoles.fragmentRefs, key < left)
    : ∃ next,
        RunRefines keys next left right
          (eraseCompletionRun
            ((RecordedExecution.completeListValue schema resolvers variables fuel
                itemType fields sources path index usages context route).run
              left))
          (eraseCompletionRun
            ((EagerRecordedExecution.completeListValue schema resolvers variables fuel
                itemType (fields.map (field keys)) sources path index (usages.map keys)
                (context.map (fragment keys)) route).run
              right)) := by
  simpa only [completeListValue_erases, EagerErasure.completeListValue_erases]
    using list_run_of_values schema resolvers variables fuel
      (valueRunConstruction_holds schema resolvers variables fuel) itemType fields sources
      path index usages context keys left right supplies ordered usageBound contextBound

theorem value_fatal_positive (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues) (fuel : Nat) (fieldType : TypeRef)
    (fields : List FieldDetails) (source : ResolverValue ObjectRef) (path : ResponsePath)
    (usages : List Nat) (context : DeferMap) (allowStream : Bool) (route : List Nat)
    (supply : Nat)
    : ∀ errors,
        ((RecordedExecution.completeValue schema resolvers variables fuel fieldType fields
            source path usages context allowStream route).run
            supply).1.report.outcome
          = .error errors
        → 0 < errors := by
  have erased := congrArg (fun output => output.1.result)
    (completeValue_erases schema resolvers variables fuel fieldType fields source path usages context
      allowStream route supply)
  simpa only [eraseCompletionRun, erase_result, ← erased, BasicErrors.PositiveFailure]
    using (ScheduledExecution.completeValue_positive schema resolvers variables fuel
            fieldType fields source path usages context allowStream supply).1

theorem field_fatal_positive (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues) (fuel : Nat) (parentType : Name)
    (source : ResolverValue ObjectRef) (name : Name) (fields : List FieldDetails)
    (path : ResponsePath) (usages : List Nat) (context : DeferMap) (route : List Nat)
    (supply : Nat)
    : ∀ errors,
        ((RecordedExecution.executeResponseField schema resolvers variables fuel
            parentType source name fields path usages context route).run
            supply).1.report.outcome
          = .error errors
        → 0 < errors := by
  have erased := congrArg (fun output => output.1.result)
    (executeResponseField_erases schema resolvers variables fuel parentType source name fields path usages
      context route supply)
  simpa only [eraseCompletionRun, erase_result, ← erased, BasicErrors.PositiveFailure]
    using (ScheduledExecution.executeResponseField_positive schema resolvers variables
            fuel parentType source name fields path usages context supply).1

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.OriginAccounting
