import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.ScheduledWorkRefinement
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.ScheduledPositivity

/-! Constructed recursive leaf correspondence for literal resolver trees: null, scalar
and arbitrarily nested finite lists, but no resolver-owned objects. With stream disabled,
these actual executions allocate no fresh keys, including the eager suffix skipped after
a fatal cut. An eligible outer stream allocates the same single boundary key; recursively
changed item counts retain their positions and fatal stop. Both roots construct full
CompletionRefines id. Object collection, allocation gaps and native records remain open. -/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.ScheduledWork

open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Semantics
open ScheduledErrors (ResultRefines)

attribute [local simp] id_pure_eq id_bind_eq id_map_eq run_bind run_map

-----------------------------------------------------------------------------------------
-- Literal leaf domain and actual paired executions with no allocation
-----------------------------------------------------------------------------------------

/-- Literal resolver trees contain no object references or subfield collection sites. -/
inductive LiteralValue : ResolverValue ObjectRef → Prop where
  | null : LiteralValue .null
  | scalar (value) : LiteralValue (.scalar value)
  | list {values} (items : ∀ value ∈ values, LiteralValue value)
    : LiteralValue (.list values)

/-- The paired actual runs relate results/Work, and neither changes its initial supply. -/
def NoStreamRefines (scheduled eager : StateM Nat (Completion α)) : Prop :=
  ∀ supply,
    CompletionRefines id (scheduled.run supply).1 (eager.run supply).1
    ∧ (scheduled.run supply).2 = supply
    ∧ (eager.run supply).2 = supply

theorem NoStreamRefines.pure (value : α)
    : NoStreamRefines (pure (Completion.pure value)) (pure (Completion.pure value)) :=
  fun _ => ⟨CompletionRefines.pure id value, rfl, rfl⟩

theorem NoStreamRefines.error (errors : Nat)
    : NoStreamRefines (Pure.pure (Completion.error errors : Completion α))
        (Pure.pure (Completion.error errors : Completion α)) :=
  fun _ => ⟨CompletionRefines.error (ResultRefines.refl _), rfl, rfl⟩

theorem NoStreamRefines.map {scheduled eager : StateM Nat (Completion α)}
    (known : NoStreamRefines scheduled eager) (wrap : Completion α → Completion β)
    (preserves
      : ∀ left right,
          CompletionRefines id left right → CompletionRefines id (wrap left) (wrap right))
    : NoStreamRefines
        (do
          let completed ← scheduled; return wrap completed)
        (do
          let completed ← eager; return wrap completed) := by
  intro supply
  obtain ⟨related, before, after⟩ := known supply
  simpa only [run_bind, StateT.run_pure, id_pure_eq]
    using And.intro (preserves _ _ related) (And.intro before after)

/-- Actual recursive completion of every literal tree, with stream disabled. -/
def LiteralNoStreamRefinement : Prop :=
  ∀ (ObjectRef : Type) (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues) fuel fieldType fields (value : ResolverValue ObjectRef)
    path usages context,
    LiteralValue value
    → NoStreamRefines
        (ScheduledExecution.completeValue schema resolvers variables fuel fieldType
          fields value path usages context false)
        (Execution.completeValue schema resolvers variables fuel fieldType fields value
          path usages context false)

-----------------------------------------------------------------------------------------
-- Recursive construction: value wrappers and actual ordinary/initial list cuts
-----------------------------------------------------------------------------------------

mutual
  theorem literal_completeValue_refines (schema : Schema)
      (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
      (fieldType : TypeRef) (fields : List FieldDetails) (value : ResolverValue ObjectRef)
      (path : ResponsePath) (usages : List Nat) (context : DeferMap)
      (literal : LiteralValue value)
      : NoStreamRefines
          (ScheduledExecution.completeValue schema resolvers variables fuel fieldType
            fields value path usages context false)
          (Execution.completeValue schema resolvers variables fuel fieldType fields value
            path usages context false) := by
    cases fuel with
    | zero =>
        simpa only [ScheduledExecution.completeValue, Execution.completeValue]
          using NoStreamRefines.error (α := ResponseValue) 1
    | succ fuel =>
        cases fieldType with
        | nonNull inner =>
            simpa only [ScheduledExecution.completeValue, Execution.completeValue]
              using (literal_completeValue_refines schema resolvers variables (fuel + 1)
                      inner fields value path usages context literal).map
                Completion.nonNull (fun _ _ known => known.nonNull)
        | named name =>
            cases literal with
            | null =>
                simpa only [ScheduledExecution.completeValue, Execution.completeValue]
                  using NoStreamRefines.pure ResponseValue.null
            | scalar scalar =>
                simp only [ScheduledExecution.completeValue, Execution.completeValue]
                split
                · exact NoStreamRefines.error 1
                · exact NoStreamRefines.pure (ResponseValue.scalar scalar)
            | list values =>
                simpa only [ScheduledExecution.completeValue, Execution.completeValue]
                  using NoStreamRefines.error (α := ResponseValue) 1
        | list inner =>
            cases literal with
            | null =>
                simpa only [ScheduledExecution.completeValue, Execution.completeValue]
                  using NoStreamRefines.pure ResponseValue.null
            | scalar scalar =>
                simpa only [ScheduledExecution.completeValue, Execution.completeValue]
                  using NoStreamRefines.error (α := ResponseValue) 1
            | @list values known =>
                simpa only [ScheduledExecution.completeValue, Execution.completeValue,
                  ScheduledExecution.completeListValueWithStream,
                  Execution.completeListValueWithStream, Bool.false_eq_true, ↓reduceIte]
                  using (literal_completeListValue_refines schema resolvers variables fuel
                          inner fields values path 0 usages context known).map
                    (Completion.catchNull ResponseValue.list)
                    (fun _ _ relation => relation.catchNull ResponseValue.list)
  termination_by (fuel, 1, sizeOf fieldType, 0)
  decreasing_by
    all_goals subst_vars; simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right

  theorem literal_completeListValue_refines (schema : Schema)
      (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
      (itemType : TypeRef) (fields : List FieldDetails)
      (values : List (ResolverValue ObjectRef)) (path : ResponsePath) (index : Nat)
      (usages : List Nat) (context : DeferMap)
      (literal : ∀ value ∈ values, LiteralValue value)
      : NoStreamRefines
          (ScheduledExecution.completeListValue schema resolvers variables fuel itemType
            fields values path index usages context)
          (Execution.completeListValue schema resolvers variables fuel itemType fields
            values path index usages context) := by
    cases values with
    | nil =>
        simpa only [ScheduledExecution.completeListValue, Execution.completeListValue]
          using NoStreamRefines.pure ([] : List ResponseValue)
    | cons value rest =>
        have head := literal_completeValue_refines schema resolvers variables fuel itemType
          fields value (path ++ [.index index]) usages context (literal value (by simp))
        have tail := literal_completeListValue_refines schema resolvers variables fuel
          itemType fields rest path (index + 1) usages context
          (fun value member => literal value (List.mem_cons_of_mem _ member))
        intro supply
        obtain ⟨related, headSupply, eagerHeadSupply⟩ := head supply
        obtain ⟨restRelated, tailSupply, eagerTailSupply⟩ := tail supply
        simp only [ScheduledExecution.completeListValue, Execution.completeListValue,
          run_bind, headSupply, eagerHeadSupply]
        cases outcome
              : ((ScheduledExecution.completeValue schema resolvers variables fuel
                    itemType fields value (path ++ [.index index]) usages context
                    false).run
                  supply).1.result with
        | error errors =>
            have positive :=
              (ScheduledExecution.completeValue_positive schema resolvers variables fuel
                itemType fields value (path ++ [.index index]) usages context false
                supply).1 errors outcome
            simp only [StateT.run_pure, id_pure_eq]
            refine ⟨
              CompletionRefines.fatal_cut List.cons _ ?_ positive,
              by trivial,
              eagerTailSupply
            ⟩
            simpa only [outcome] using related.1
        | ok value =>
            simp only [StateT.run_pure, id_pure_eq]
            exact ⟨related.combine List.cons restRelated, tailSupply, eagerTailSupply⟩
  termination_by (fuel, 2, sizeOf itemType, sizeOf values)
  decreasing_by
    all_goals subst_vars; simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right
    all_goals try omega
end

theorem literalNoStreamRefinement_holds : LiteralNoStreamRefinement := by
  intro ObjectRef schema resolvers variables fuel fieldType fields value path usages context
    literal
  exact literal_completeValue_refines schema resolvers variables fuel fieldType fields
    value path usages context literal

-----------------------------------------------------------------------------------------
-- Actual stream tails: related recursive payloads retain the same stop/item positions
-----------------------------------------------------------------------------------------

theorem literal_completeStreamItems_refines (schema : Schema)
    (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
    (itemType : TypeRef) (fields : List FieldDetails)
    (values : List (ResolverValue ObjectRef)) (path : ResponsePath) (index : Nat)
    (literal : ∀ value ∈ values, LiteralValue value) (supply : Nat)
    : ItemsRefine id
        ((ScheduledExecution.completeStreamItems schema resolvers variables fuel itemType
            fields values path index).run
          supply).1
        ((Execution.completeStreamItems schema resolvers variables fuel itemType fields
            values path index).run
          supply).1
      ∧ ((ScheduledExecution.completeStreamItems schema resolvers variables fuel itemType
            fields values path index).run
          supply).2
        = supply
      ∧ ((Execution.completeStreamItems schema resolvers variables fuel itemType fields
            values path index).run
          supply).2
        = supply := by
  induction values generalizing index with
  | nil =>
      simp only [ScheduledExecution.completeStreamItems, Execution.completeStreamItems]
      exact ⟨.nil, rfl, rfl⟩
  | cons value rest ih =>
      obtain ⟨related, headSupply, eagerHeadSupply⟩ :=
        literal_completeValue_refines schema resolvers variables fuel itemType fields value
          (path ++ [.index index]) [] [] (literal value (by simp)) supply
      have restLiteral : ∀ value ∈ rest, LiteralValue value :=
        fun value member => literal value (List.mem_cons_of_mem _ member)
      obtain ⟨tail, tailSupply, eagerTailSupply⟩ := ih (index + 1) restLiteral
      have same := related.1.1
      simp only [ScheduledExecution.completeStreamItems, Execution.completeStreamItems,
        run_bind, headSupply, eagerHeadSupply]
      cases outcome :
            ((ScheduledExecution.completeValue schema resolvers variables fuel itemType
                fields value (path ++ [.index index]) [] [] false).run supply).1.result
      <;> cases eagerOutcome :
            ((Execution.completeValue schema resolvers variables fuel itemType fields value
                (path ++ [.index index]) [] [] false).run supply).1.result
      <;> simp only [ScheduledErrors.SameData, outcome, eagerOutcome] at same
      · simp only [StateT.run_pure, id_pure_eq]
        refine ⟨.cons ?_ .empty .nil, by trivial, by trivial⟩
        simpa only [outcome, eagerOutcome] using related.1
      · simp only [StateT.run_pure, id_pure_eq, run_bind]
        refine ⟨.cons ?_ related.2 tail, tailSupply, eagerTailSupply⟩
        simpa only [outcome, eagerOutcome] using related.1

-----------------------------------------------------------------------------------------
-- Outer stream boundary allocates the same single key in the literal fragment
-----------------------------------------------------------------------------------------

/-- Related actual runs may allocate, but finish at the same supply in this fragment. -/
def LiteralRunRefines (scheduled eager : StateM Nat (Completion α)) : Prop :=
  ∀ supply,
    CompletionRefines id (scheduled.run supply).1 (eager.run supply).1
    ∧ (scheduled.run supply).2 = (eager.run supply).2

theorem NoStreamRefines.literal {scheduled eager : StateM Nat (Completion α)}
    (known : NoStreamRefines scheduled eager)
    : LiteralRunRefines scheduled eager := by
  intro supply
  obtain ⟨related, before, after⟩ := known supply
  exact ⟨related, before.trans after.symm⟩

theorem LiteralRunRefines.map {scheduled eager : StateM Nat (Completion α)}
    (known : LiteralRunRefines scheduled eager) (wrap : Completion α → Completion β)
    (preserves
      : ∀ left right,
          CompletionRefines id left right → CompletionRefines id (wrap left) (wrap right))
    : LiteralRunRefines
        (do
          let completed ← scheduled; return wrap completed)
        (do
          let completed ← eager; return wrap completed) := by
  intro supply
  obtain ⟨related, same⟩ := known supply
  simpa only [run_bind, StateT.run_pure, id_pure_eq]
    using And.intro (preserves _ _ related) same

theorem literal_completeListValueWithStream_refines (schema : Schema)
    (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
    (itemType : TypeRef) (fields : List FieldDetails)
    (values : List (ResolverValue ObjectRef)) (path : ResponsePath)
    (usages : List Nat) (context : DeferMap) (allowStream : Bool)
    (literal : ∀ value ∈ values, LiteralValue value)
    : LiteralRunRefines
        (ScheduledExecution.completeListValueWithStream schema resolvers variables fuel
          itemType fields values path usages context allowStream)
        (Execution.completeListValueWithStream schema resolvers variables fuel itemType
          fields values path usages context allowStream) := by
  cases usageResult
        : (if allowStream then
              getStreamUsage variables
                (fields.head?.map FieldDetails.directives |>.getD [])
            else
              .ok none) with
  | error errors =>
      intro supply
      simp only [ScheduledExecution.completeListValueWithStream,
        Execution.completeListValueWithStream, usageResult]
      exact ⟨⟨ResultRefines.refl _, .empty⟩, by trivial⟩
  | ok option =>
      cases option with
      | none =>
          simpa only [ScheduledExecution.completeListValueWithStream,
            Execution.completeListValueWithStream, usageResult]
            using (literal_completeListValue_refines schema resolvers variables fuel
                    itemType fields values path 0 usages context literal).literal.map
              (Completion.catchNull ResponseValue.list)
              (fun _ _ known => known.catchNull ResponseValue.list)
      | some usage =>
          intro supply
          have initialLiteral : ∀ value ∈ values.take usage.initialCount, LiteralValue value :=
            fun value member => literal value (List.mem_of_mem_take member)
          obtain ⟨related, initialSupply, eagerInitialSupply⟩ :=
            literal_completeListValue_refines schema resolvers variables fuel itemType
              fields (values.take usage.initialCount) path 0 usages context initialLiteral
              supply
          have same := related.1.1
          simp only [ScheduledExecution.completeListValueWithStream,
            Execution.completeListValueWithStream, usageResult, run_bind,
            initialSupply, eagerInitialSupply]
          cases outcome :
                ((ScheduledExecution.completeListValue schema resolvers variables fuel
                    itemType fields (values.take usage.initialCount) path 0 usages context).run
                  supply).1.result
          <;> cases eagerOutcome :
                ((Execution.completeListValue schema resolvers variables fuel itemType fields
                    (values.take usage.initialCount) path 0 usages context).run supply).1.result
          <;> simp only [ScheduledErrors.SameData, outcome, eagerOutcome] at same
          · simp only [StateT.run_pure, id_pure_eq]
            exact ⟨related.catchNull ResponseValue.list, by trivial⟩
          · simp only
            split
            · simp only [StateT.run_pure, id_pure_eq]
              exact ⟨related.catchNull ResponseValue.list, by trivial⟩
            · have remainingLiteral : ∀ value ∈ values.drop usage.initialCount,
                    LiteralValue value :=
                fun value member => literal value (List.mem_of_mem_drop member)
              obtain ⟨tail, tailSupply, eagerTailSupply⟩ :=
                literal_completeStreamItems_refines schema resolvers variables fuel
                  itemType (fields.map (fun field => { field with deferUsage := none }))
                  (values.drop usage.initialCount) path usage.initialCount remainingLiteral
                  (supply + 1)
              simp only [freshNodeRef, run_bind, StateT.run_get, StateT.run_set,
                StateT.run_pure, id_pure_eq]
              exact ⟨⟨(related.catchNull ResponseValue.list).1,
                .combine (related.catchNull ResponseValue.list).2 (.stream tail)⟩,
                tailSupply.trans eagerTailSupply.symm⟩

/-- All literal completions, including outer stream boundaries and recursively changed
stream-item counts, relate full Completion/Work and finish at the same fresh supply. -/
def LiteralCompletionRefinement : Prop :=
  ∀ (ObjectRef : Type) (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues) fuel fieldType fields (value : ResolverValue ObjectRef)
    path usages context allowStream,
    LiteralValue value
    → LiteralRunRefines
        (ScheduledExecution.completeValue schema resolvers variables fuel fieldType
          fields value path usages context allowStream)
        (Execution.completeValue schema resolvers variables fuel fieldType fields value
          path usages context allowStream)

theorem literal_completeValue_withStream_refines (schema : Schema)
    (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
    (fieldType : TypeRef) (fields : List FieldDetails) (value : ResolverValue ObjectRef)
    (path : ResponsePath) (usages : List Nat) (context : DeferMap) (allowStream : Bool)
    (literal : LiteralValue value)
    : LiteralRunRefines
        (ScheduledExecution.completeValue schema resolvers variables fuel fieldType
          fields value path usages context allowStream)
        (Execution.completeValue schema resolvers variables fuel fieldType fields value
          path usages context allowStream) := by
  induction fieldType generalizing fuel with
  | nonNull inner ih =>
      cases fuel with
      | zero =>
          simpa only [ScheduledExecution.completeValue, Execution.completeValue]
            using (NoStreamRefines.error (α := ResponseValue) 1).literal
      | succ fuel =>
          simpa only [ScheduledExecution.completeValue, Execution.completeValue]
            using (ih (fuel + 1)).map Completion.nonNull (fun _ _ known => known.nonNull)
  | named name =>
      cases fuel with
      | zero =>
          simpa only [ScheduledExecution.completeValue, Execution.completeValue]
            using (NoStreamRefines.error (α := ResponseValue) 1).literal
      | succ fuel =>
          cases literal with
          | null =>
              simpa only [ScheduledExecution.completeValue, Execution.completeValue]
                using (NoStreamRefines.pure ResponseValue.null).literal
          | scalar scalar =>
              simp only [ScheduledExecution.completeValue, Execution.completeValue]
              split
              · exact (NoStreamRefines.error 1).literal
              · exact (NoStreamRefines.pure (ResponseValue.scalar scalar)).literal
          | list items =>
              simpa only [ScheduledExecution.completeValue, Execution.completeValue]
                using (NoStreamRefines.error (α := ResponseValue) 1).literal
  | list inner _ =>
      cases fuel with
      | zero =>
          simpa only [ScheduledExecution.completeValue, Execution.completeValue]
            using (NoStreamRefines.error (α := ResponseValue) 1).literal
      | succ fuel =>
          cases literal with
          | null =>
              simpa only [ScheduledExecution.completeValue, Execution.completeValue]
                using (NoStreamRefines.pure ResponseValue.null).literal
          | scalar scalar =>
              simpa only [ScheduledExecution.completeValue, Execution.completeValue]
                using (NoStreamRefines.error (α := ResponseValue) 1).literal
          | @list values known =>
              simpa only [ScheduledExecution.completeValue, Execution.completeValue]
                using literal_completeListValueWithStream_refines schema resolvers
                  variables fuel inner fields values path usages context allowStream known

theorem literalCompletionRefinement_holds : LiteralCompletionRefinement := by
  intro ObjectRef schema resolvers variables fuel fieldType fields value path usages context
    allowStream literal
  exact literal_completeValue_withStream_refines schema resolvers variables fuel fieldType
    fields value path usages context allowStream literal

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.ScheduledWork
