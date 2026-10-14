import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.ScheduledWorkRefinement
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.ScheduledSiblingRefinement

/-! Full Completion/Work composition through actual field/list cuts. Paired recursive
actions must use one compatible map throughout the scope and carry the chosen supply
relation forward. This is a checked reduction, not the general construction of those
child witnesses/maps. A fatal parent discards both Work trees, but may skip allocations. -/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.ScheduledWork

open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Semantics
open ScheduledErrors

attribute [local simp] id_pure_eq id_bind_eq id_map_eq run_bind run_map

/-- Paired actual child runs with full Work correspondence and positive cut failures. -/
def ActionWorkRefines (keys : Nat → Nat) (supplies : Nat → Nat → Prop)
    (scheduled eager : StateM Nat (Completion α))
    : Prop :=
  ∀ left right,
    supplies left right
    → CompletionRefines keys (scheduled.run left).1 (eager.run right).1
      ∧ supplies (scheduled.run left).2 (eager.run right).2
      ∧ BasicErrors.PositiveFailure (scheduled.run left).1.result

/-- Ordered child actions using the same map and actual supply relation. -/
inductive PairedWorkActions (keys : Nat → Nat) (supplies : Nat → Nat → Prop)
    : List (StateM Nat (Completion α)) → List (StateM Nat (Completion α)) → Prop where
  | nil : PairedWorkActions keys supplies [] []
  | cons {scheduled eager scheduledRest eagerRest}
    (head : ActionWorkRefines keys supplies scheduled eager)
    (rest : PairedWorkActions keys supplies scheduledRest eagerRest)
    : PairedWorkActions keys supplies (scheduled :: scheduledRest) (eager :: eagerRest)

/-- Paired recursive children construct full parent correspondence. A nonfatal parent
also retains the supply relation; a fatal parent's skipped suffix can allocate a gap. -/
def SiblingWorkRefinement : Prop :=
  ∀ (α β : Type) keys (supplies : Nat → Nat → Prop) (combine : α → β → β) (base : β)
    (scheduled eager : List (StateM Nat (Completion α))) left right,
    PairedWorkActions keys supplies scheduled eager
    → supplies left right
    → CompletionRefines keys ((cutActions combine base scheduled).run left).1
        ((executeActions combine base eager).run right).1
      ∧ (isFatal ((cutActions combine base scheduled).run left).1.result = false
          → supplies ((cutActions combine base scheduled).run left).2
              ((executeActions combine base eager).run right).2)

theorem siblingWorkRefinement_holds : SiblingWorkRefinement := by
  intro α β keys supplies combine base scheduled eager left right paired initial
  induction paired generalizing left right with
  | nil => exact ⟨CompletionRefines.pure keys base, fun _ => initial⟩
  | @cons scheduledHead eagerHead scheduledTail eagerTail head rest ih =>
      obtain ⟨refined, next, positive⟩ := head left right initial
      rw [cutActions_cons]
      simp only [executeActions, run_bind]
      cases result : (scheduledHead.run left).1.result with
      | error errors =>
          simp only [StateT.run_pure, id_pure_eq, Completion.error, isFatal,
            Bool.true_eq_false, false_implies, and_true]
          apply CompletionRefines.fatal_cut combine _ _ (positive errors result)
          simpa only [result] using refined.1
      | ok value =>
          obtain ⟨tail, later⟩ := ih _ _ next
          simp only [run_bind, StateT.run_pure, id_pure_eq]
          refine ⟨refined.combine combine tail, ?_⟩
          intro healthy
          rw [completion_combine_result, isFatal_combine, result] at healthy
          exact later (by simpa only [isFatal, Bool.false_or] using healthy)

-----------------------------------------------------------------------------------------
-- Actual-call-site reductions, with recursive child premises explicit
-----------------------------------------------------------------------------------------

theorem executeCollectedFields_work_refines_of_children
    (schema : Schema) (resolvers : Resolvers ObjectRef) (variables : VariableValues)
    (fuel : Nat) (parentType : Name) (source : ResolverValue ObjectRef)
    (cutFields eagerFields : CollectedFieldsMap) (path : ResponsePath)
    (cutUsages eagerUsages : List Nat) (cutContext eagerContext : DeferMap)
    (keys : Nat → Nat) (supplies : Nat → Nat → Prop) (left right : Nat)
    (children
      : PairedWorkActions keys supplies
          (ScheduledExecution.fieldActions schema resolvers variables fuel parentType
            source cutFields path cutUsages cutContext)
          (ScheduledErrors.fieldActions schema resolvers variables fuel parentType source
            eagerFields path eagerUsages eagerContext))
    (initial : supplies left right)
    : CompletionRefines keys
        ((ScheduledExecution.executeCollectedFields schema resolvers variables fuel
            parentType source cutFields path cutUsages cutContext).run
          left).1
        ((Execution.executeCollectedFields schema resolvers variables fuel parentType
            source eagerFields path eagerUsages eagerContext).run
          right).1
      ∧ (isFatal
              ((ScheduledExecution.executeCollectedFields schema resolvers variables fuel
                  parentType source cutFields path cutUsages cutContext).run
                left).1.result
            = false
          → supplies
              ((ScheduledExecution.executeCollectedFields schema resolvers variables fuel
                  parentType source cutFields path cutUsages cutContext).run
                left).2
              ((Execution.executeCollectedFields schema resolvers variables fuel
                  parentType source eagerFields path eagerUsages eagerContext).run
                right).2) := by
  rw [ScheduledExecution.executeCollectedFields_actions,
    ScheduledErrors.executeCollectedFields_actions]
  exact siblingWorkRefinement_holds _ _ keys supplies List.append [] _ _ left right
    children initial

theorem completeListValue_work_refines_of_children
    (schema : Schema) (resolvers : Resolvers ObjectRef) (variables : VariableValues)
    (fuel : Nat) (itemType : TypeRef) (cutFields eagerFields : List FieldDetails)
    (values : List (ResolverValue ObjectRef)) (path : ResponsePath) (index : Nat)
    (cutUsages eagerUsages : List Nat) (cutContext eagerContext : DeferMap)
    (keys : Nat → Nat) (supplies : Nat → Nat → Prop) (left right : Nat)
    (children
      : PairedWorkActions keys supplies
          (ScheduledExecution.listActions schema resolvers variables fuel itemType
            cutFields path cutUsages cutContext values index)
          (ScheduledErrors.listActions schema resolvers variables fuel itemType
            eagerFields path eagerUsages eagerContext values index))
    (initial : supplies left right)
    : CompletionRefines keys
        ((ScheduledExecution.completeListValue schema resolvers variables fuel itemType
            cutFields values path index cutUsages cutContext).run
          left).1
        ((Execution.completeListValue schema resolvers variables fuel itemType eagerFields
            values path index eagerUsages eagerContext).run
          right).1 := by
  rw [ScheduledExecution.completeListValue_actions, ScheduledErrors.completeListValue_actions]
  exact (siblingWorkRefinement_holds _ _ keys supplies List.cons [] _ _ left right
    children initial).1

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.ScheduledWork
