import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.SiblingWorkRefinement
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.ScheduledLiteralRefinement

/-! Constructed full field-scope correspondence when its resolved field values are
literal trees. Each recursive field witness comes from the actual lookup/coercion/
resolver/completion branches. A scope cut can skip a later stream allocation; equal
supplies are concluded only for nonfatal scopes. Object-valued fields and recursive
deferred-plan map construction remain outside this root. -/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.ScheduledWork

open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Semantics
open ScheduledErrors (isFatal ResultRefines)

/-- Domain restriction on actual resolver successes, not on desired execution outputs. -/
def LiteralFieldValues (resolvers : Resolvers ObjectRef) (parentType : Name)
    (source : ResolverValue ObjectRef) (fields : List FieldDetails)
    : Prop :=
  ∀ field ∈ fields,
    ∀ arguments value,
      resolveFieldValue resolvers parentType field.fieldName arguments source = some value
      → LiteralValue value

/-- Every selected field group's successful resolutions are literal trees. -/
def LiteralFields (resolvers : Resolvers ObjectRef) (parentType : Name)
    (source : ResolverValue ObjectRef) (fields : CollectedFieldsMap)
    : Prop :=
  ∀ entry ∈ fields, LiteralFieldValues resolvers parentType source entry.2

private theorem literal_pure_result (result : Result α)
    : LiteralRunRefines (Pure.pure ({ result } : Completion α))
        (Pure.pure ({ result } : Completion α)) :=
  fun _ => ⟨⟨ResultRefines.refl result, .empty⟩, rfl⟩

theorem literal_executeResponseField_refines (schema : Schema)
    (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
    (parentType : Name) (source : ResolverValue ObjectRef) (name : Name)
    (fields : List FieldDetails) (path : ResponsePath) (usages : List Nat)
    (context : DeferMap) (literal : LiteralFieldValues resolvers parentType source fields)
    : LiteralRunRefines
        (ScheduledExecution.executeResponseField schema resolvers variables fuel
          parentType source name fields path usages context)
        (Semantics.executeResponseField schema resolvers variables fuel parentType source
          name fields path usages context) := by
  cases fuel with
  | zero =>
      simpa only [ScheduledExecution.executeResponseField, Semantics.executeResponseField,
        Completion.error]
        using literal_pure_result (α := List (Name × ResponseValue)) (.error 1)
  | succ fuel =>
      cases fields with
      | nil =>
          simpa only [ScheduledExecution.executeResponseField,
            Semantics.executeResponseField, Completion.error]
            using literal_pure_result (α := List (Name × ResponseValue)) (.error 1)
      | cons field rest =>
          simp only [ScheduledExecution.executeResponseField, Semantics.executeResponseField]
          split
          · simp_all only [Completion.error]
            exact literal_pure_result _
          · simp_all only
            split
            · simp_all only
              exact literal_pure_result _
            · rename_i arguments _
              simp_all only
              split
              · simp_all only
                exact literal_pure_result _
              · rename_i resolved known
                simp_all only
                exact (literal_completeValue_withStream_refines schema resolvers variables
                  fuel _ (field :: rest) resolved (path ++ [.field name]) usages context true
                  (literal field (by simp) arguments resolved known)).map
                    (Completion.map (fun value => [(name, value)]))
                    (fun _ _ relation => relation.map _)

theorem literal_fieldActions_paired (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues) (fuel : Nat) (parentType : Name)
    (source : ResolverValue ObjectRef) (fields : CollectedFieldsMap)
    (path : ResponsePath) (usages : List Nat) (context : DeferMap)
    (literal : LiteralFields resolvers parentType source fields)
    : PairedWorkActions id Eq
        (ScheduledExecution.fieldActions schema resolvers variables fuel parentType source
          fields path usages context)
        (ScheduledErrors.fieldActions schema resolvers variables fuel parentType source
          fields path usages context) := by
  induction fields with
  | nil => exact .nil
  | cons entry rest ih =>
      apply PairedWorkActions.cons
      · intro left right same
        subst right
        obtain ⟨related, supplies⟩ := literal_executeResponseField_refines schema resolvers
          variables fuel parentType source entry.1 entry.2 path usages context
          (literal entry (by simp)) left
        exact ⟨related, supplies,
          (ScheduledExecution.executeResponseField_positive schema resolvers variables fuel
            parentType source entry.1 entry.2 path usages context left).1⟩
      · exact ih (fun entry member => literal entry (List.mem_cons_of_mem _ member))

/-- Actual field-scope relation constructed from a resolver-domain restriction; no
paired-child or output Work premise is assumed. Final supplies agree only without a cut. -/
def LiteralFieldScopeRefinement : Prop :=
  ∀ (ObjectRef : Type) (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues) fuel parentType (source : ResolverValue ObjectRef)
    fields path usages context supply,
    LiteralFields resolvers parentType source fields
    → CompletionRefines id
        ((ScheduledExecution.executeCollectedFields schema resolvers variables fuel
            parentType source fields path usages context).run
          supply).1
        ((Execution.executeCollectedFields schema resolvers variables fuel parentType
            source fields path usages context).run
          supply).1
      ∧ (isFatal
              ((ScheduledExecution.executeCollectedFields schema resolvers variables fuel
                  parentType source fields path usages context).run
                supply).1.result
            = false
          → ((ScheduledExecution.executeCollectedFields schema resolvers variables fuel
                parentType source fields path usages context).run
              supply).2
            = ((Execution.executeCollectedFields schema resolvers variables fuel
                  parentType source fields path usages context).run
                supply).2)

theorem literalFieldScopeRefinement_holds : LiteralFieldScopeRefinement := by
  intro ObjectRef schema resolvers variables fuel parentType source fields path usages context
    supply literal
  exact executeCollectedFields_work_refines_of_children schema resolvers variables fuel
    parentType source fields fields path usages usages context context id Eq supply supply
    (literal_fieldActions_paired schema resolvers variables fuel parentType source fields path
      usages context literal) rfl

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.ScheduledWork
