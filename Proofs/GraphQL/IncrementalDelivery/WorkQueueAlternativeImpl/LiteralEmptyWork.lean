import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.LiteralOriginConstruction

/-! No hidden deferred or streamed reports in nonstreaming literal completion.
Work association is preserved: the result may contain combine nodes, but every leaf
is empty. This is stronger than a zero-error inventory or a missing top-level stream. -/

namespace
  GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.OriginAccounting

open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Semantics
open ScheduledWork (LiteralValue)

inductive EmptyRecordedWork : RecordedWork → Prop where
  | empty : EmptyRecordedWork .empty
  | combine {left right} (head : EmptyRecordedWork left) (tail : EmptyRecordedWork right)
    : EmptyRecordedWork (.combine left right)

theorem EmptyRecordedWork.origins {work} (known : EmptyRecordedWork work)
    : work.origins = [] := by
  induction known with
  | empty => simp only [RecordedWork.origins]
  | combine head tail ihLeft ihRight => simp only [RecordedWork.origins, ihLeft, ihRight,
      List.nil_append]

theorem EmptyRecordedWork.map (f : α → β) {completed : RecordedCompletion α}
    (known : EmptyRecordedWork completed.work)
    : EmptyRecordedWork (completed.map f).work := by
  cases outcome : completed.report.outcome
  <;> simp only [RecordedCompletion.map, outcome]
  · exact .empty
  · exact known

theorem EmptyRecordedWork.catchNull (f : α → ResponseValue)
    {completed : RecordedCompletion α} (known : EmptyRecordedWork completed.work)
    : EmptyRecordedWork (completed.catchNull f).work := by
  cases outcome : completed.report.outcome
  <;> simp only [RecordedCompletion.catchNull, outcome]
  · exact .empty
  · exact known

theorem EmptyRecordedWork.nonNull (route : List Nat)
    {completed : RecordedCompletion ResponseValue}
    (known : EmptyRecordedWork completed.work)
    : EmptyRecordedWork (completed.nonNull route).work := by
  cases outcome : (completed.report.nonNull route).outcome
  <;> simp only [RecordedCompletion.nonNull, outcome]
  · exact .empty
  · exact known

theorem EmptyRecordedWork.completionCombine (f : α → β → γ)
    {left : RecordedCompletion α} {right : RecordedCompletion β}
    (head : EmptyRecordedWork left.work) (tail : EmptyRecordedWork right.work)
    : EmptyRecordedWork (RecordedCompletion.combine f left right).work := by
  cases outcome : (Report.combine f left.report right.report).outcome
  <;> simp only [RecordedCompletion.combine, outcome]
  · exact .empty
  · exact .combine head tail

attribute [local simp] id_pure_eq id_bind_eq id_map_eq run_bind run_map

mutual
  theorem literal_value_emptyWork (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variables : VariableValues) (fuel : Nat) (fieldType : TypeRef)
      (fields : List FieldDetails) (source : ResolverValue ObjectRef)
      (path : ResponsePath) (usages : List Nat) (context : DeferMap) (route : List Nat)
      (supply : Nat) (literal : LiteralValue source)
      : EmptyRecordedWork
          ((RecordedExecution.completeValue schema resolvers variables fuel fieldType
              fields source path usages context false route).run
            supply).1.work
        ∧ EmptyRecordedWork
            ((EagerRecordedExecution.completeValue schema resolvers variables fuel
                fieldType fields source path usages context false route).run
              supply).1.work := by
    cases fuel with
    | zero =>
        simp only [RecordedExecution.completeValue, EagerRecordedExecution.completeValue,
        StateT.run_pure, id_pure_eq, RecordedCompletion.fault]; exact ⟨.empty, .empty⟩
    | succ fuel =>
        cases fieldType with
        | nonNull inner =>
            obtain ⟨cut, eager⟩ := literal_value_emptyWork schema resolvers variables (fuel + 1) inner
              fields source path usages context (route ++ [0]) supply literal
            simpa only [RecordedExecution.completeValue,
              EagerRecordedExecution.completeValue, run_bind, StateT.run_pure, id_pure_eq]
              using And.intro (cut.nonNull route) (eager.nonNull route)
        | named name =>
            cases literal with
            | null =>
                simp only [RecordedExecution.completeValue, EagerRecordedExecution.completeValue,
                StateT.run_pure, id_pure_eq, RecordedCompletion.pure]; exact ⟨.empty, .empty⟩
            | scalar scalar =>
                simp only [RecordedExecution.completeValue, EagerRecordedExecution.completeValue]
                split <;> exact ⟨.empty, .empty⟩
            | list sources =>
                simp only [RecordedExecution.completeValue, EagerRecordedExecution.completeValue,
                StateT.run_pure, id_pure_eq, RecordedCompletion.fault]; exact ⟨.empty, .empty⟩
        | list inner =>
            cases literal with
            | null =>
                simp only [RecordedExecution.completeValue, EagerRecordedExecution.completeValue,
                StateT.run_pure, id_pure_eq, RecordedCompletion.pure]; exact ⟨.empty, .empty⟩
            | scalar scalar =>
                simp only [RecordedExecution.completeValue, EagerRecordedExecution.completeValue,
                StateT.run_pure, id_pure_eq, RecordedCompletion.fault]; exact ⟨.empty, .empty⟩
            | @list sources known =>
                obtain ⟨cut, eager⟩ := literal_items_emptyWork schema resolvers variables fuel inner
                  fields sources path 0 usages context (route ++ [0] ++ [0]) supply known
                simpa only [RecordedExecution.completeValue,
                  EagerRecordedExecution.completeValue,
                  RecordedExecution.completeListValueWithStream,
                  EagerRecordedExecution.completeListValueWithStream, Bool.false_eq_true,
                  ↓reduceIte, run_bind, StateT.run_pure, id_pure_eq]
                  using And.intro (cut.catchNull ResponseValue.list)
                    (eager.catchNull ResponseValue.list)
  termination_by (fuel, 1, sizeOf fieldType, 0)
  decreasing_by
    all_goals subst_vars; simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right

  theorem literal_items_emptyWork (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variables : VariableValues) (fuel : Nat) (itemType : TypeRef)
      (fields : List FieldDetails) (sources : List (ResolverValue ObjectRef))
      (path : ResponsePath) (index : Nat) (usages : List Nat) (context : DeferMap)
      (route : List Nat) (supply : Nat)
      (literal : ∀ source ∈ sources, LiteralValue source)
      : EmptyRecordedWork
          ((RecordedExecution.completeListValue schema resolvers variables fuel itemType
              fields sources path index usages context route).run
            supply).1.work
        ∧ EmptyRecordedWork
            ((EagerRecordedExecution.completeListValue schema resolvers variables fuel
                itemType fields sources path index usages context route).run
              supply).1.work := by
    cases sources with
    | nil =>
        simp only [RecordedExecution.completeListValue, EagerRecordedExecution.completeListValue,
        StateT.run_pure, id_pure_eq, RecordedCompletion.pure]; exact ⟨.empty, .empty⟩
    | cons source rest =>
        obtain ⟨cutHead, eagerHead⟩ := literal_value_emptyWork schema resolvers variables fuel itemType
          fields source (path ++ [.index index]) usages context (route ++ [0]) supply
          (literal source (by simp))
        have cutTail := (literal_items_emptyWork schema resolvers variables fuel itemType fields rest
          path (index + 1) usages context (route ++ [1])
          ((RecordedExecution.completeValue schema resolvers variables fuel itemType fields source
            (path ++ [.index index]) usages context false (route ++ [0])).run supply).2
          (fun source member => literal source (List.mem_cons_of_mem _ member))).1
        have eagerTail := (literal_items_emptyWork schema resolvers variables fuel itemType fields rest
          path (index + 1) usages context (route ++ [1])
          ((EagerRecordedExecution.completeValue schema resolvers variables fuel itemType fields source
            (path ++ [.index index]) usages context false (route ++ [0])).run supply).2
          (fun source member => literal source (List.mem_cons_of_mem _ member))).2
        simp only [RecordedExecution.completeListValue, EagerRecordedExecution.completeListValue,
          run_bind]
        refine ⟨?_, ?_⟩
        · split
          · exact cutHead.map (fun value => [value])
          · simpa only [run_bind, StateT.run_pure, id_pure_eq]
              using cutHead.completionCombine List.cons cutTail
        · simpa only [StateT.run_pure, id_pure_eq]
            using eagerHead.completionCombine List.cons eagerTail
  termination_by (fuel, 2, sizeOf itemType, sizeOf sources)
  decreasing_by
    all_goals subst_vars; simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right
    all_goals try omega
end

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.OriginAccounting
