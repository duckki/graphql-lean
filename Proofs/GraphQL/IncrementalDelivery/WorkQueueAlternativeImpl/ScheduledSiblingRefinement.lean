import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.SiblingResultRefinement
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.ScheduledPositivity

/-! Actual recursive field/list call sites for the conditional sibling-refinement edge.
Action lists use ScheduledExecution recursively on the cut side and original public
execution on the eager side. Paired child-action refinement remains an explicit leaf
obligation; it is not assumed as a public queue/execution invariant. -/

namespace
  GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.ScheduledExecution

open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Semantics
open ScheduledErrors

attribute [local simp] id_pure_eq id_bind_eq id_map_eq run_bind run_map

/-- Bubbling results have no retained semantic work. Native resource cleanup is not
asserted by this proof predicate. -/
def FailureForm (completed : Completion α) : Prop :=
  ∀ errors, completed.result = .error errors → completed = .error errors

private theorem error_form (errors : Nat)
    : FailureForm (Completion.error errors : Completion α) := by
  intro later same
  cases same
  rfl

private theorem map_form (wrap : α → β) (completed : Completion α)
    : FailureForm (completed.map wrap) := by
  intro errors failed
  cases result : completed.result with
  | error count =>
      simp only [Completion.map, result, Completion.error] at failed ⊢
      cases failed
      rfl
  | ok value => simp [Completion.map, result] at failed

/-- Derived from the actual field branches, not an assumed invariant on an arbitrary
completion supplied to the sibling fold. -/
theorem executeResponseField_failure_form (schema : Schema)
    (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
    (parentType : Name) (source : ResolverValue ObjectRef) (name : Name)
    (fields : List FieldDetails) (path : ResponsePath) (usages : List Nat)
    (context : DeferMap)
    : RunEnsures FailureForm
        (executeResponseField schema resolvers variables fuel parentType source name
          fields path usages context) := by
  cases fuel with
  | zero => simpa only [executeResponseField] using runEnsures_pure _ _ (error_form 1)
  | succ fuel =>
      cases fields with
      | nil => simpa only [executeResponseField] using runEnsures_pure _ _ (error_form 1)
      | cons field rest =>
          simp only [executeResponseField]
          split
          · exact runEnsures_pure _ _ (error_form 1)
          · rename_i definition _
            have failed : FailureForm
                ({ result := singleFieldResult name (handleFieldError definition.outputType) }
                  : Completion _) := by
              cases definition.outputType <;>
                simp [FailureForm, singleFieldResult, handleFieldError, Completion.error]
            split
            · exact runEnsures_pure _ _ failed
            · split
              · exact runEnsures_pure _ _ failed
              · refine runEnsures_bind (fun _ : Completion ResponseValue => True) _ _ _
                  (fun _ => trivial) ?_
                intro completed _
                exact runEnsures_pure _ _ (map_form _ completed)

/-- Child actions use this recursively cut executor, not original eager completion. -/
def fieldActions (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues) (fuel : Nat) (parentType : Name)
    (source : ResolverValue ObjectRef) (fields : CollectedFieldsMap)
    (path : ResponsePath) (usages : List Nat) (context : DeferMap)
    : List (StateM Nat (Completion (List (Name × ResponseValue)))) :=
  fields.map
    (fun entry =>
      executeResponseField schema resolvers variables fuel parentType
        source entry.1 entry.2 path usages context)

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

/-- Exact decomposition of recursively cut fields, including Work and final supply. -/
theorem executeCollectedFields_actions (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues) (fuel : Nat) (parentType : Name)
    (source : ResolverValue ObjectRef) (fields : CollectedFieldsMap)
    (path : ResponsePath) (usages : List Nat) (context : DeferMap)
    : executeCollectedFields schema resolvers variables fuel parentType source fields
        path usages context
      = cutActions List.append []
          (fieldActions schema resolvers variables fuel parentType source fields path
            usages context) := by
  induction fields with
  | nil =>
      simp only [executeCollectedFields, fieldActions, List.map_nil, cutActions,
        observeUntilFatal]
      rfl
  | cons entry rest ih =>
      rcases entry with ⟨name, group⟩
      simp only [executeCollectedFields, fieldActions, List.map_cons, cutActions_cons]
      funext supply
      change StateT.run _ supply = StateT.run _ supply
      simp only [run_bind]
      cases failed
            : ((executeResponseField schema resolvers variables fuel parentType source
                  name group path usages context).run
                supply).1.result with
      | error errors =>
          have form := executeResponseField_failure_form schema resolvers variables fuel
            parentType source name group path usages context supply errors failed
          simp only [StateT.run_pure, id_pure_eq, form]
      | ok value => simp only [ih, fieldActions]

/-- Exact decomposition of recursively cut ordinary/initial list items. -/
theorem completeListValue_actions (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues) (fuel : Nat) (itemType : TypeRef)
    (fields : List FieldDetails) (values : List (ResolverValue ObjectRef))
    (path : ResponsePath) (index : Nat) (usages : List Nat) (context : DeferMap)
    : completeListValue schema resolvers variables fuel itemType fields values path index
        usages context
      = cutActions List.cons []
          (listActions schema resolvers variables fuel itemType fields path usages context
            values index) := by
  induction values generalizing index with
  | nil =>
      simp only [completeListValue, listActions, cutActions, observeUntilFatal]
      rfl
  | cons value rest ih =>
      simp only [completeListValue, listActions, cutActions_cons, ih]
      funext supply
      change StateT.run _ supply = StateT.run _ supply
      simp only [run_bind]
      cases ((completeValue schema resolvers variables fuel itemType fields value
        (path ++ [.index index]) usages context false).run supply).1.result <;> rfl

-----------------------------------------------------------------------------------------
-- Checked actual-call-site reductions; recursive child correspondence is still explicit
-----------------------------------------------------------------------------------------

theorem executeCollectedFields_result_refines_of_children
    (schema : Schema) (resolvers : Resolvers ObjectRef) (variables : VariableValues)
    (fuel : Nat) (parentType : Name) (source : ResolverValue ObjectRef)
    (cutFields eagerFields : CollectedFieldsMap) (path : ResponsePath)
    (cutUsages eagerUsages : List Nat) (cutContext eagerContext : DeferMap)
    (supplies : Nat → Nat → Prop) (left right : Nat)
    (children
      : PairedActions supplies
          (fieldActions schema resolvers variables fuel parentType source cutFields path
            cutUsages cutContext)
          (ScheduledErrors.fieldActions schema resolvers variables fuel parentType source
            eagerFields path eagerUsages eagerContext))
    (initial : supplies left right)
    : ResultRefines
        ((executeCollectedFields schema resolvers variables fuel parentType source
            cutFields path cutUsages cutContext).run
          left).1.result
        ((Execution.executeCollectedFields schema resolvers variables fuel parentType
            source eagerFields path eagerUsages eagerContext).run
          right).1.result := by
  rw [executeCollectedFields_actions, ScheduledErrors.executeCollectedFields_actions]
  exact (siblingResultRefinement_holds _ _ supplies List.append [] _ _ left right
    children initial).1

theorem completeListValue_result_refines_of_children
    (schema : Schema) (resolvers : Resolvers ObjectRef) (variables : VariableValues)
    (fuel : Nat) (itemType : TypeRef) (cutFields eagerFields : List FieldDetails)
    (values : List (ResolverValue ObjectRef)) (path : ResponsePath) (index : Nat)
    (cutUsages eagerUsages : List Nat) (cutContext eagerContext : DeferMap)
    (supplies : Nat → Nat → Prop) (left right : Nat)
    (children
      : PairedActions supplies
          (listActions schema resolvers variables fuel itemType cutFields path cutUsages
            cutContext values index)
          (ScheduledErrors.listActions schema resolvers variables fuel itemType
            eagerFields path eagerUsages eagerContext values index))
    (initial : supplies left right)
    : ResultRefines
        ((completeListValue schema resolvers variables fuel itemType cutFields values path
            index cutUsages cutContext).run
          left).1.result
        ((Execution.completeListValue schema resolvers variables fuel itemType eagerFields
            values path index eagerUsages eagerContext).run
          right).1.result := by
  rw [completeListValue_actions, ScheduledErrors.completeListValue_actions]
  exact (siblingResultRefinement_holds _ _ supplies List.cons [] _ _ left right children
    initial).1

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.ScheduledExecution
