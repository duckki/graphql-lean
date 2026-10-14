import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.ScheduledErrors
import Proofs.GraphQL.IncrementalDelivery.Semantics.FieldExecution
import Proofs.GraphQL.IncrementalDelivery.Semantics.Collection

/-! Construct sibling plans by observing the existing eager executor's actual actions.
The full completion and final fresh-key supply are preserved. This does not execute a
short-circuiting query or infer native settlements/resources from pure completion.
-/

namespace
  GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.ScheduledErrors

open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Semantics (
  id_pure_eq id_bind_eq id_map_eq run_bind run_map)

attribute [local simp] id_pure_eq id_bind_eq id_map_eq run_bind run_map

-----------------------------------------------------------------------------------------
-- Instrument existing sibling actions, retaining their complete outcomes and final supply
-----------------------------------------------------------------------------------------

/-- Observe complete public action outcomes in the same order and at the same supplies. -/
def observeActions : List (StateM Nat (Completion α)) → StateM Nat (List (Completion α))
  | [] => pure []
  | action :: rest => do
      let completed ← action
      let later ← observeActions rest
      return completed :: later

def foldCompletions (combine : α → β → β) (base : β) : List (Completion α) → Completion β
  | [] => .pure base
  | completed :: rest =>
      Completion.combine combine completed (foldCompletions combine base rest)

/-- A decomposition of the original eager fold, not an optimized execution policy. -/
def executeActions (combine : α → β → β) (base : β)
    : List (StateM Nat (Completion α)) → StateM Nat (Completion β)
  | [] => pure (.pure base)
  | action :: rest => do
      let completed ← action
      let later ← executeActions combine base rest
      return Completion.combine combine completed later

/-- Ghost position IDs do not allocate execution keys or change the observed outcomes. -/
def completionPlan : List (Completion α) → Nat → List (Sibling α)
  | [], _ => []
  | completed :: rest, id =>
      ⟨id, completed.result⟩ :: completionPlan rest (id + 1)

/-- Exact decomposition includes all data, counted errors, work, and final key supply. -/
theorem executeActions_observed (combine : α → β → β) (base : β)
    (actions : List (StateM Nat (Completion α))) (supply : Nat)
    : (executeActions combine base actions).run supply
      = let observed := (observeActions actions).run supply
        (foldCompletions combine base observed.1, observed.2) := by
  induction actions generalizing supply with
  | nil => rfl
  | cons action rest ih =>
      simp only [executeActions, observeActions, run_bind, StateT.run_pure, id_pure_eq]
      rw [ih]
      rfl

theorem foldCompletions_errors (combine : α → β → β) (base : β)
    (completions : List (Completion α)) (id : Nat)
    : countedErrors (foldCompletions combine base completions).result
      = errorTotal (completionPlan completions id) := by
  induction completions generalizing id with
  | nil => rfl
  | cons completed rest ih =>
      have combined : countedErrors (Completion.combine combine completed
          (foldCompletions combine base rest)).result
        = countedErrors completed.result
          + countedErrors (foldCompletions combine base rest).result := by
        unfold Completion.combine
        cases outcome : GraphQL.Execution.Result.combine combine completed.result
            (foldCompletions combine base rest).result
        <;> simpa only [Completion.error, countedErrors, outcome]
          using countedErrors_combine combine completed.result
            (foldCompletions combine base rest).result
      simpa only [foldCompletions, completionPlan, errorTotal, List.map_cons,
        List.sum_cons]
        using combined.trans
          (congrArg (fun count => countedErrors completed.result + count) (ih (id + 1)))

/-- Every observed public action has a distinct response-position ID. -/
theorem completionPlan_ids (completions : List (Completion α)) (id : Nat)
    : (completionPlan completions id).map Sibling.id
      = List.range' id completions.length := by
  induction completions generalizing id with
  | nil => rfl
  | cons completed rest ih =>
      simp only [completionPlan, List.map_cons, List.length_cons, List.range'_succ, ih]

theorem completionPlan_unique (completions : List (Completion α)) (id : Nat)
    : ((completionPlan completions id).map Sibling.id).Nodup := by
  rw [completionPlan_ids]
  exact List.nodup_range'

theorem foldCompletions_cons_result (completions : List (Completion α)) (id : Nat)
    : (foldCompletions List.cons [] completions).result
      = eager (completionPlan completions id) := by
  induction completions generalizing id with
  | nil => rfl
  | cons completed rest ih =>
      have combined : (Completion.combine List.cons completed
          (foldCompletions List.cons [] rest)).result
        = GraphQL.Execution.Result.combine List.cons completed.result
          (foldCompletions List.cons [] rest).result := by
        unfold Completion.combine
        cases GraphQL.Execution.Result.combine List.cons completed.result
          (foldCompletions List.cons [] rest).result <;> rfl
      simp only [foldCompletions, completionPlan, eager, combined]
      rw [ih (id + 1)]

-----------------------------------------------------------------------------------------
-- Actual list/field traversals, using the original recursive completions
-----------------------------------------------------------------------------------------

def listActions (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues) (fuel : Nat) (itemType : TypeRef)
    (fields : List FieldDetails) (path : ResponsePath) (usages : List Nat)
    (context : DeferMap)
    : List (ResolverValue ObjectRef) → Nat → List (StateM Nat (Completion ResponseValue))
  | [], _ => []
  | value :: rest, index =>
      completeValue schema resolvers variables fuel itemType fields value
        (path ++ [.index index]) usages context false
      :: listActions schema resolvers variables fuel itemType fields path usages context
          rest (index + 1)

def fieldActions (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues) (fuel : Nat) (parentType : Name)
    (source : ResolverValue ObjectRef) (fields : CollectedFieldsMap)
    (path : ResponsePath) (usages : List Nat) (context : DeferMap)
    : List (StateM Nat (Completion (List (Name × ResponseValue)))) :=
  fields.map
    (fun entry =>
      Semantics.executeResponseField schema resolvers variables fuel
        parentType source entry.1 entry.2 path usages context)

theorem completeListValue_actions (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues) (fuel : Nat) (itemType : TypeRef)
    (fields : List FieldDetails) (values : List (ResolverValue ObjectRef))
    (path : ResponsePath) (index : Nat) (usages : List Nat) (context : DeferMap)
    : completeListValue schema resolvers variables fuel itemType fields values path index
        usages context
      = executeActions List.cons []
          (listActions schema resolvers variables fuel itemType fields path usages context
            values index) := by
  induction values generalizing index with
  | nil => simp only [completeListValue, executeActions, listActions]
  | cons value rest ih => simp only [completeListValue, listActions, executeActions, ih]

theorem executeCollectedFields_actions (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues) (fuel : Nat) (parentType : Name)
    (source : ResolverValue ObjectRef) (fields : CollectedFieldsMap)
    (path : ResponsePath) (usages : List Nat) (context : DeferMap)
    : executeCollectedFields schema resolvers variables fuel parentType source fields
        path usages context
      = executeActions List.append []
          (fieldActions schema resolvers variables fuel parentType source fields path
            usages context) := by
  induction fields with
  | nil => exact Semantics.executeCollectedFields_nil ..
  | cons entry rest ih =>
      obtain ⟨name, group⟩ := entry
      rw [Semantics.executeCollectedFields_cons]
      simp only [fieldActions, List.map_cons, executeActions] at ih ⊢
      rw [ih]

/-- Constructed observations explain the full actual list completion and supply. -/
theorem completeListValue_observed (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues) (fuel : Nat) (itemType : TypeRef)
    (fields : List FieldDetails) (values : List (ResolverValue ObjectRef))
    (path : ResponsePath) (index : Nat) (usages : List Nat) (context : DeferMap)
    (supply : Nat)
    : (completeListValue schema resolvers variables fuel itemType fields values path index
        usages context).run
        supply
      = let observed :=
          (observeActions
            (listActions schema resolvers variables fuel itemType
              fields path usages context values index)).run
            supply
        (foldCompletions List.cons [] observed.1, observed.2) := by
  rw [completeListValue_actions]
  exact executeActions_observed ..

/-- Constructed observations explain the full actual field completion and supply. -/
theorem executeCollectedFields_observed (schema : Schema)
    (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
    (parentType : Name) (source : ResolverValue ObjectRef) (fields : CollectedFieldsMap)
    (path : ResponsePath) (usages : List Nat) (context : DeferMap) (supply : Nat)
    : (executeCollectedFields schema resolvers variables fuel parentType source fields
        path usages context).run
        supply
      = let observed :=
          (observeActions
            (fieldActions schema resolvers variables fuel parentType
              source fields path usages context)).run
            supply
        (foldCompletions List.append [] observed.1, observed.2) := by
  rw [executeCollectedFields_actions]
  exact executeActions_observed ..

-----------------------------------------------------------------------------------------
-- Scheduled count conservation against those constructed public-execution outcomes
-----------------------------------------------------------------------------------------

/-- Checked composition against an actual public list result. The scope history must
still be derived from native execution; it is not a new premise of queue conformance.
-/
theorem completeListValue_scheduled_errors (schema : Schema)
    (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
    (itemType : TypeRef) (fields : List FieldDetails)
    (values : List (ResolverValue ObjectRef)) (path : ResponsePath) (index : Nat)
    (usages : List Nat) (context : DeferMap) (supply : Nat) (scope : Scope ResponseValue)
    (history
      : History
          (completionPlan
            ((observeActions
                (listActions schema resolvers variables
                  fuel itemType fields path usages context values index)).run
              supply).1
            index)
          scope)
    : scope.reportedErrors + errorTotal scope.pending + errorTotal scope.cancelled
      = countedErrors
          ((completeListValue schema resolvers variables fuel itemType fields
              values path index usages context).run
            supply).1.result := by
  rw [completeListValue_observed]
  dsimp only
  rw [foldCompletions_errors _ _ _ index]
  exact history.error_accounting.trans (eager_errors _)

/-- The generic complete-scope observation now compares to the actual public list result,
not to an independently selected outcome list. Native recursive cuts remain separate.
-/
theorem completeListValue_scheduled_observation (schema : Schema)
    (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
    (itemType : TypeRef) (fields : List FieldDetails)
    (values : List (ResolverValue ObjectRef)) (path : ResponsePath) (index : Nat)
    (usages : List Nat) (context : DeferMap) (supply : Nat) (scope : Scope ResponseValue)
    (history
      : History
          (completionPlan
            ((observeActions
                (listActions schema resolvers variables
                  fuel itemType fields path usages context values index)).run
              supply).1
            index)
          scope)
    (complete : scope.pending = [])
    : ∃ observed,
        scope.observe
            (completionPlan
              ((observeActions
                  (listActions schema resolvers variables
                    fuel itemType fields path usages context values index)).run
                supply).1
              index)
          = some observed
        ∧ SameData observed
            ((completeListValue schema resolvers variables fuel itemType fields
                values path index usages context).run
              supply).1.result
        ∧ countedErrors observed = scope.reportedErrors
        ∧ countedErrors observed + errorTotal scope.cancelled
          = countedErrors
              ((completeListValue schema resolvers variables fuel itemType fields
                  values path index usages context).run
                supply).1.result := by
  rw [completeListValue_observed]
  dsimp only
  rw [foldCompletions_cons_result _ index]
  exact history.complete_observation complete

/-- The field version also retains preceding nullable errors and actual eager key supply. -/
theorem executeCollectedFields_scheduled_errors (schema : Schema)
    (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
    (parentType : Name) (source : ResolverValue ObjectRef) (fields : CollectedFieldsMap)
    (path : ResponsePath) (usages : List Nat) (context : DeferMap) (supply : Nat)
    (scope : Scope (List (Name × ResponseValue)))
    (history
      : History
          (completionPlan
            ((observeActions
                (fieldActions schema resolvers variables
                  fuel parentType source fields path usages context)).run
              supply).1
            0)
          scope)
    : scope.reportedErrors + errorTotal scope.pending + errorTotal scope.cancelled
      = countedErrors
          ((executeCollectedFields schema resolvers variables fuel parentType source
              fields path usages context).run
            supply).1.result := by
  rw [executeCollectedFields_observed]
  dsimp only
  rw [foldCompletions_errors _ _ _ 0]
  exact history.error_accounting.trans (eager_errors _)

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.ScheduledErrors
