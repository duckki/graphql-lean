import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.EagerOriginErasure
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.OriginRefinement
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.ScheduledLiteralRefinement

/-! Constructed originating-reference coverage for actual literal completion trees.
Nulls, scalars and arbitrary nested finite lists are included; resolver-owned objects
and subfield collection are not. Only the outer list may stream. No child output relation
is a premise, and eager sibling errors remain aggregated. Native records remain separate. -/

namespace
  GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.OriginAccounting

open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Semantics
open ScheduledWork (LiteralValue)

attribute [local simp] id_pure_eq id_bind_eq id_map_eq run_bind run_map

/-- Both actual inventories are related, and neither run changes its input supply. -/
def NoStreamOriginsRefine (cut eager : StateM Nat (RecordedCompletion α)) : Prop :=
  ∀ supply,
    CompletionOriginsRefine (cut.run supply).1 (eager.run supply).1
    ∧ (cut.run supply).2 = supply
    ∧ (eager.run supply).2 = supply

theorem NoStreamOriginsRefine.pure (value : α)
    : NoStreamOriginsRefine (pure (RecordedCompletion.pure value))
        (pure (RecordedCompletion.pure value)) :=
  fun _ => ⟨CompletionOriginsRefine.pure _, rfl, rfl⟩

theorem NoStreamOriginsRefine.fault (route : List Nat) (outcome : Result α)
    : NoStreamOriginsRefine (Pure.pure (RecordedCompletion.fault route outcome))
        (Pure.pure (RecordedCompletion.fault route outcome)) :=
  fun _ => ⟨CompletionOriginsRefine.fault _ _, rfl, rfl⟩

theorem NoStreamOriginsRefine.map {cut eager : StateM Nat (RecordedCompletion α)}
    (known : NoStreamOriginsRefine cut eager)
    (wrap : RecordedCompletion α → RecordedCompletion β)
    (preserves
      : ∀ left right,
          CompletionOriginsRefine left right
          → CompletionOriginsRefine (wrap left) (wrap right))
    : NoStreamOriginsRefine
        (do
          let completed ← cut; return wrap completed)
        (do
          let completed ← eager; return wrap completed) := by
  intro supply
  obtain ⟨related, before, after⟩ := known supply
  simpa only [run_bind, StateT.run_pure, id_pure_eq]
    using And.intro (preserves _ _ related) (And.intro before after)

mutual
  theorem literal_completeValue_origins (schema : Schema)
      (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
      (fieldType : TypeRef) (fields : List FieldDetails) (value : ResolverValue ObjectRef)
      (path : ResponsePath) (usages : List Nat) (context : DeferMap) (route : List Nat)
      (literal : LiteralValue value)
      : NoStreamOriginsRefine
          (RecordedExecution.completeValue schema resolvers variables fuel fieldType
            fields value path usages context false route)
          (EagerRecordedExecution.completeValue schema resolvers variables fuel fieldType
            fields value path usages context false route) := by
    cases fuel with
    | zero =>
        simpa only [RecordedExecution.completeValue, EagerRecordedExecution.completeValue]
          using NoStreamOriginsRefine.fault route (.error 1 : Result ResponseValue)
    | succ fuel =>
        cases fieldType with
        | nonNull inner =>
            simpa only [RecordedExecution.completeValue,
              EagerRecordedExecution.completeValue]
              using (literal_completeValue_origins schema resolvers variables (fuel + 1)
                      inner fields value path usages context (route ++ [0]) literal).map
                (RecordedCompletion.nonNull route) (fun _ _ known => known.nonNull route)
        | named name =>
            cases literal with
            | null =>
                simpa only [RecordedExecution.completeValue,
                  EagerRecordedExecution.completeValue]
                  using NoStreamOriginsRefine.pure ResponseValue.null
            | scalar scalar =>
                simp only [RecordedExecution.completeValue, EagerRecordedExecution.completeValue]
                split
                · exact NoStreamOriginsRefine.fault route (.error 1)
                · exact NoStreamOriginsRefine.pure (ResponseValue.scalar scalar)
            | list items =>
                simpa only [RecordedExecution.completeValue,
                  EagerRecordedExecution.completeValue]
                  using NoStreamOriginsRefine.fault route
                    (.error 1 : Result ResponseValue)
        | list inner =>
            cases literal with
            | null =>
                simpa only [RecordedExecution.completeValue,
                  EagerRecordedExecution.completeValue]
                  using NoStreamOriginsRefine.pure ResponseValue.null
            | scalar scalar =>
                simpa only [RecordedExecution.completeValue,
                  EagerRecordedExecution.completeValue]
                  using NoStreamOriginsRefine.fault route
                    (.error 1 : Result ResponseValue)
            | @list values known =>
                simpa only [RecordedExecution.completeValue,
                  EagerRecordedExecution.completeValue,
                  RecordedExecution.completeListValueWithStream,
                  EagerRecordedExecution.completeListValueWithStream, Bool.false_eq_true,
                  ↓reduceIte, List.append_assoc]
                  using (literal_completeListValue_origins schema resolvers variables fuel
                          inner fields values path 0 usages context
                          (route ++ ([0] ++ [0])) known).map
                    (RecordedCompletion.catchNull ResponseValue.list)
                    (fun _ _ related => related.catchNull ResponseValue.list)
  termination_by (fuel, 1, sizeOf fieldType, 0)
  decreasing_by
    all_goals subst_vars; simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right

  theorem literal_completeListValue_origins (schema : Schema)
      (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
      (itemType : TypeRef) (fields : List FieldDetails)
      (values : List (ResolverValue ObjectRef)) (path : ResponsePath) (index : Nat)
      (usages : List Nat) (context : DeferMap) (route : List Nat)
      (literal : ∀ value ∈ values, LiteralValue value)
      : NoStreamOriginsRefine
          (RecordedExecution.completeListValue schema resolvers variables fuel itemType
            fields values path index usages context route)
          (EagerRecordedExecution.completeListValue schema resolvers variables fuel
            itemType fields values path index usages context route) := by
    cases values with
    | nil =>
        simpa only [RecordedExecution.completeListValue,
          EagerRecordedExecution.completeListValue]
          using NoStreamOriginsRefine.pure ([] : List ResponseValue)
    | cons value rest =>
        have head := literal_completeValue_origins schema resolvers variables fuel itemType
          fields value (path ++ [.index index]) usages context (route ++ [0])
          (literal value (by simp))
        have tail := literal_completeListValue_origins schema resolvers variables fuel
          itemType fields rest path (index + 1) usages context (route ++ [1])
          (fun value member => literal value (List.mem_cons_of_mem _ member))
        intro supply
        obtain ⟨related, headSupply, eagerHeadSupply⟩ := head supply
        obtain ⟨restRelated, tailSupply, eagerTailSupply⟩ := tail supply
        simp only [RecordedExecution.completeListValue, EagerRecordedExecution.completeListValue,
          run_bind, headSupply, eagerHeadSupply]
        cases outcome
              : ((RecordedExecution.completeValue schema resolvers variables fuel itemType
                    fields value (path ++ [.index index]) usages context false
                    (route ++ [0])).run
                  supply).1.report.outcome with
        | error errors =>
            have erased := congrArg (fun output => output.1.result)
              (completeValue_erases schema resolvers variables fuel itemType fields value
                (path ++ [.index index]) usages context false (route ++ [0]) supply)
            change _ = ((ScheduledExecution.completeValue schema resolvers variables fuel
              itemType fields value (path ++ [.index index]) usages context false).run
              supply).1.result at erased
            have positive :=
              (ScheduledExecution.completeValue_positive schema resolvers variables fuel
                itemType fields value (path ++ [.index index]) usages context false supply).1
            rw [← erased] at positive
            simp only [StateT.run_pure, id_pure_eq]
            exact ⟨
              CompletionOriginsRefine.fatal_cut List.cons (fun value => [value])
                _ related.1 outcome (positive errors outcome),
              by trivial,
              eagerTailSupply
            ⟩
        | ok value =>
            simp only [StateT.run_pure, id_pure_eq]
            exact ⟨related.combine List.cons restRelated, tailSupply, eagerTailSupply⟩
  termination_by (fuel, 2, sizeOf itemType, sizeOf values)
  decreasing_by
    all_goals subst_vars; simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right
    all_goals try omega
end

/-- Actual literal value/list completion constructs primitive-origin coverage, data
and error-presence agreement. No originating-reference correspondence is assumed. -/
def LiteralNoStreamOriginsConstruction : Prop :=
  ∀ (ObjectRef : Type) (schema : Schema) (resolvers : Resolvers ObjectRef) variables fuel
    fieldType fields (value : ResolverValue ObjectRef) path usages context route,
    LiteralValue value
    → NoStreamOriginsRefine
        (RecordedExecution.completeValue schema resolvers variables fuel fieldType fields
          value path usages context false route)
        (EagerRecordedExecution.completeValue schema resolvers variables fuel fieldType
          fields value path usages context false route)

theorem literalNoStreamOriginsConstruction_holds
    : LiteralNoStreamOriginsConstruction := by
  intro ObjectRef schema resolvers variables fuel fieldType fields value path usages context route
    literal
  exact literal_completeValue_origins schema resolvers variables fuel fieldType fields value
    path usages context route literal

-----------------------------------------------------------------------------------------
-- Actual stream reports retain the same item positions and primitive references
-----------------------------------------------------------------------------------------

theorem literal_completeStreamItems_origins (schema : Schema)
    (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
    (itemType : TypeRef) (fields : List FieldDetails)
    (values : List (ResolverValue ObjectRef)) (path : ResponsePath) (index : Nat)
    (route : List Nat) (literal : ∀ value ∈ values, LiteralValue value) (supply : Nat)
    : ItemOriginsRefine
        ((RecordedExecution.completeStreamItems schema resolvers variables fuel itemType
            fields values path index route).run
          supply).1
        ((EagerRecordedExecution.completeStreamItems schema resolvers variables fuel
            itemType fields values path index route).run
          supply).1
      ∧ ((RecordedExecution.completeStreamItems schema resolvers variables fuel itemType
            fields values path index route).run
          supply).2
        = supply
      ∧ ((EagerRecordedExecution.completeStreamItems schema resolvers variables fuel
            itemType fields values path index route).run
          supply).2
        = supply := by
  induction values generalizing index route with
  | nil =>
      simp only [RecordedExecution.completeStreamItems, EagerRecordedExecution.completeStreamItems]
      exact ⟨.nil, rfl, rfl⟩
  | cons value rest ih =>
      obtain ⟨related, headSupply, eagerHeadSupply⟩ :=
        literal_completeValue_origins schema resolvers variables fuel itemType fields value
          (path ++ [.index index]) [] [] (route ++ [0]) (literal value (by simp)) supply
      have restLiteral : ∀ value ∈ rest, LiteralValue value :=
        fun value member => literal value (List.mem_cons_of_mem _ member)
      obtain ⟨tail, tailSupply, eagerTailSupply⟩ := ih (index + 1) (route ++ [1]) restLiteral
      have same := related.1.1.1
      simp only [RecordedExecution.completeStreamItems, EagerRecordedExecution.completeStreamItems,
        run_bind, headSupply, eagerHeadSupply]
      cases outcome :
          ((RecordedExecution.completeValue schema resolvers variables fuel itemType fields value
            (path ++ [.index index]) [] [] false (route ++ [0])).run supply).1.report.outcome
      <;> cases eagerOutcome :
          ((EagerRecordedExecution.completeValue schema resolvers variables fuel itemType fields
            value (path ++ [.index index]) [] [] false (route ++ [0])).run supply).1.report.outcome
      <;> simp only [ScheduledErrors.SameData, outcome, eagerOutcome] at same
      · simp only [StateT.run_pure, id_pure_eq]
        exact ⟨.cons related.1 .empty .nil, by trivial, by trivial⟩
      · simp only [StateT.run_pure, id_pure_eq, run_bind]
        exact ⟨.cons related.1 related.2 tail, tailSupply, eagerTailSupply⟩

/-- An outer stream may allocate a boundary, but both actual runs finish together. -/
def LiteralOriginsRunRefines (cut eager : StateM Nat (RecordedCompletion α)) : Prop :=
  ∀ supply,
    CompletionOriginsRefine (cut.run supply).1 (eager.run supply).1
    ∧ (cut.run supply).2 = (eager.run supply).2

theorem NoStreamOriginsRefine.literal {cut eager : StateM Nat (RecordedCompletion α)}
    (known : NoStreamOriginsRefine cut eager)
    : LiteralOriginsRunRefines cut eager := by
  intro supply
  obtain ⟨related, before, after⟩ := known supply
  exact ⟨related, before.trans after.symm⟩

theorem LiteralOriginsRunRefines.map {cut eager : StateM Nat (RecordedCompletion α)}
    (known : LiteralOriginsRunRefines cut eager)
    (wrap : RecordedCompletion α → RecordedCompletion β)
    (preserves
      : ∀ left right,
          CompletionOriginsRefine left right
          → CompletionOriginsRefine (wrap left) (wrap right))
    : LiteralOriginsRunRefines
        (do
          let completed ← cut; return wrap completed)
        (do
          let completed ← eager; return wrap completed) := by
  intro supply
  obtain ⟨related, final⟩ := known supply
  simpa only [run_bind, StateT.run_pure, id_pure_eq]
    using And.intro (preserves _ _ related) final

theorem literal_completeListValueWithStream_origins (schema : Schema)
    (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
    (itemType : TypeRef) (fields : List FieldDetails)
    (values : List (ResolverValue ObjectRef)) (path : ResponsePath)
    (usages : List Nat) (context : DeferMap) (allowStream : Bool) (route : List Nat)
    (literal : ∀ value ∈ values, LiteralValue value)
    : LiteralOriginsRunRefines
        (RecordedExecution.completeListValueWithStream schema resolvers variables fuel
          itemType fields values path usages context allowStream route)
        (EagerRecordedExecution.completeListValueWithStream schema resolvers variables
          fuel itemType fields values path usages context allowStream route) := by
  cases usageResult
        : (if allowStream then
              getStreamUsage variables
                (fields.head?.map FieldDetails.directives |>.getD [])
            else
              .ok none) with
  | error errors =>
      intro supply
      simp only [RecordedExecution.completeListValueWithStream,
        EagerRecordedExecution.completeListValueWithStream, usageResult]
      exact ⟨CompletionOriginsRefine.fault _ _, by trivial⟩
  | ok option =>
      cases option with
      | none =>
          simpa only [RecordedExecution.completeListValueWithStream,
            EagerRecordedExecution.completeListValueWithStream, usageResult]
            using (literal_completeListValue_origins schema resolvers variables fuel
                    itemType fields values path 0 usages context (route ++ [0])
                    literal).literal.map
              (RecordedCompletion.catchNull ResponseValue.list)
              (fun _ _ known => known.catchNull ResponseValue.list)
      | some usage =>
          intro supply
          have initialLiteral : ∀ value ∈ values.take usage.initialCount, LiteralValue value :=
            fun value member => literal value (List.mem_of_mem_take member)
          obtain ⟨related, initialSupply, eagerInitialSupply⟩ :=
            literal_completeListValue_origins schema resolvers variables fuel itemType fields
              (values.take usage.initialCount) path 0 usages context (route ++ [0])
              initialLiteral supply
          have same := related.1.1.1
          simp only [RecordedExecution.completeListValueWithStream,
            EagerRecordedExecution.completeListValueWithStream, usageResult, run_bind,
            initialSupply, eagerInitialSupply]
          cases outcome :
              ((RecordedExecution.completeListValue schema resolvers variables fuel itemType
                fields (values.take usage.initialCount) path 0 usages context (route ++ [0])).run
                supply).1.report.outcome
          <;> cases eagerOutcome :
              ((EagerRecordedExecution.completeListValue schema resolvers variables fuel itemType
                fields (values.take usage.initialCount) path 0 usages context (route ++ [0])).run
                supply).1.report.outcome
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
                literal_completeStreamItems_origins schema resolvers variables fuel itemType
                  (fields.map (fun field => { field with deferUsage := none }))
                  (values.drop usage.initialCount) path usage.initialCount (route ++ [1])
                  remainingLiteral (supply + 1)
              simp only [freshNodeRef, run_bind, StateT.run_get, StateT.run_set,
                StateT.run_pure, id_pure_eq]
              exact ⟨⟨(related.catchNull ResponseValue.list).1,
                .combine (related.catchNull ResponseValue.list).2 (.stream tail)⟩,
                tailSupply.trans eagerTailSupply.symm⟩

/-- Actual arbitrary finite literal completion, including the outer stream boundary
and retained tail reports. General object/subfield recursion is a separate target. -/
def LiteralOriginsConstruction : Prop :=
  ∀ (ObjectRef : Type) (schema : Schema) (resolvers : Resolvers ObjectRef)
    variables fuel fieldType fields (value : ResolverValue ObjectRef) path usages context
    allowStream route,
    LiteralValue value
    → LiteralOriginsRunRefines
        (RecordedExecution.completeValue schema resolvers variables fuel fieldType fields
          value path usages context allowStream route)
        (EagerRecordedExecution.completeValue schema resolvers variables fuel fieldType
          fields value path usages context allowStream route)

theorem literal_completeValue_withStream_origins (schema : Schema)
    (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
    (fieldType : TypeRef) (fields : List FieldDetails) (value : ResolverValue ObjectRef)
    (path : ResponsePath) (usages : List Nat) (context : DeferMap) (allowStream : Bool)
    (route : List Nat) (literal : LiteralValue value)
    : LiteralOriginsRunRefines
        (RecordedExecution.completeValue schema resolvers variables fuel fieldType fields
          value path usages context allowStream route)
        (EagerRecordedExecution.completeValue schema resolvers variables fuel fieldType
          fields value path usages context allowStream route) := by
  induction fieldType generalizing fuel route with
  | nonNull inner ih =>
      cases fuel with
      | zero =>
          simpa only [RecordedExecution.completeValue,
            EagerRecordedExecution.completeValue]
            using (NoStreamOriginsRefine.fault route
                    (.error 1 : Result ResponseValue)).literal
      | succ fuel =>
          simpa only [RecordedExecution.completeValue,
            EagerRecordedExecution.completeValue]
            using (ih (fuel + 1) (route ++ [0])).map (RecordedCompletion.nonNull route)
              (fun _ _ known => known.nonNull route)
  | named name =>
      cases fuel with
      | zero =>
          simpa only [RecordedExecution.completeValue,
            EagerRecordedExecution.completeValue]
            using (NoStreamOriginsRefine.fault route
                    (.error 1 : Result ResponseValue)).literal
      | succ fuel =>
          cases literal with
          | null =>
              simpa only [RecordedExecution.completeValue,
                EagerRecordedExecution.completeValue]
                using (NoStreamOriginsRefine.pure ResponseValue.null).literal
          | scalar scalar =>
              simp only [RecordedExecution.completeValue, EagerRecordedExecution.completeValue]
              split
              · exact (NoStreamOriginsRefine.fault route (.error 1)).literal
              · exact (NoStreamOriginsRefine.pure (ResponseValue.scalar scalar)).literal
          | list items =>
              simpa only [RecordedExecution.completeValue,
                EagerRecordedExecution.completeValue]
                using (NoStreamOriginsRefine.fault route
                        (.error 1 : Result ResponseValue)).literal
  | list inner _ =>
      cases fuel with
      | zero =>
          simpa only [RecordedExecution.completeValue,
            EagerRecordedExecution.completeValue]
            using (NoStreamOriginsRefine.fault route
                    (.error 1 : Result ResponseValue)).literal
      | succ fuel =>
          cases literal with
          | null =>
              simpa only [RecordedExecution.completeValue,
                EagerRecordedExecution.completeValue]
                using (NoStreamOriginsRefine.pure ResponseValue.null).literal
          | scalar scalar =>
              simpa only [RecordedExecution.completeValue,
                EagerRecordedExecution.completeValue]
                using (NoStreamOriginsRefine.fault route
                        (.error 1 : Result ResponseValue)).literal
          | @list values known =>
              simpa only [RecordedExecution.completeValue,
                EagerRecordedExecution.completeValue]
                using literal_completeListValueWithStream_origins schema resolvers
                  variables fuel inner fields values path usages context allowStream
                  (route ++ [0]) known

theorem literalOriginsConstruction_holds : LiteralOriginsConstruction := by
  intro ObjectRef schema resolvers variables fuel fieldType fields value path usages context
    allowStream route literal
  exact literal_completeValue_withStream_origins schema resolvers variables fuel fieldType
    fields value path usages context allowStream route literal

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.OriginAccounting
