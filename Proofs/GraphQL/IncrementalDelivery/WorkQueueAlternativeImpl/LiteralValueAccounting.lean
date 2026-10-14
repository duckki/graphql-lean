import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.LiteralStreamAccounting

/-! Actual literal value cut accounting, including outer streams and non-null
wrappers. Bubbling retains initial error identities and prunes future cut inventories
exactly when both actual completions discard that Work. Native timing remains outside
this pure finite construction. -/

namespace
  GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.OriginAccounting

open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Semantics
open ScheduledWork (LiteralValue)

theorem Report.nonNull_unique (route : List Nat) (report : Report ResponseValue)
    (unique : report.origins.Nodup)
    : (report.nonNull route).origins.Nodup := by
  obtain ⟨outcome, origins, accounts⟩ := report
  cases outcome with
  | error errors => exact unique
  | ok value =>
      obtain ⟨value, errors⟩ := value
      cases value <;> cases errors <;>
        simp_all [Report.nonNull, Report.fault, primitiveOrigins, ScheduledErrors.countedErrors]

theorem ReportCutAccounting.nonNull (route : List Nat) {cut eager : Report ResponseValue}
    {sites} (known : ReportCutAccounting cut eager sites)
    : ReportCutAccounting (cut.nonNull route) (eager.nonNull route) sites := by
  have related := known.1.nonNull route
  have unique := eager.nonNull_unique route known.2.2.1
  refine ⟨related, ⟨?_, known.2.1.2⟩, unique, related.omitted_count unique⟩
  intro origin missing
  rw [known.1.nonNull_omitted route] at missing
  exact known.2.1.1 origin missing

/-- The initial report survives bubbling. Future scopes survive only if their
actual containing completion still retains Work. -/
def StreamCutInventory.nonNull (route : List Nat) (report : Report ResponseValue)
    (inventory : StreamCutInventory)
    : StreamCutInventory :=
  match (report.nonNull route).outcome with
  | .error _ => ⟨inventory.initial, []⟩
  | .ok _ => inventory

theorem StreamCutAccounting.nonNull (route : List Nat) {cut eager inventory}
    (known : StreamCutAccounting cut eager inventory)
    : StreamCutAccounting (cut.nonNull route) (eager.nonNull route)
        (inventory.nonNull route cut.report) := by
  have report := known.1.nonNull route
  have same := report.1.1.1
  cases outcome : (cut.report.nonNull route).outcome
  <;> cases eagerOutcome : (eager.report.nonNull route).outcome
  <;> simp only [ScheduledErrors.SameData, outcome, eagerOutcome] at same
  · simpa only [StreamCutAccounting, RecordedCompletion.nonNull,
      StreamCutInventory.nonNull, outcome, eagerOutcome]
      using And.intro report
        (LiteralStreamWorkAccounting.vacant EmptyRecordedWork.empty
          EmptyRecordedWork.empty)
  · simpa only [StreamCutAccounting, RecordedCompletion.nonNull,
      StreamCutInventory.nonNull, outcome, eagerOutcome] using And.intro report known.2

namespace LiteralCuts

/-- The actual value control flow selects one retained-scope inventory. Object
references are excluded by the construction theorem, not approximated as literals. -/
def streamValue (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues) (fuel : Nat) (fieldType : TypeRef)
    (fields : List FieldDetails) (source : ResolverValue ObjectRef) (path : ResponsePath)
    (usages : List Nat) (context : DeferMap) (allowStream : Bool) (route : List Nat)
    (supply : Nat)
    : StreamCutInventory :=
  match fuel, fieldType, source with
  | 0, _, _ => ⟨[], []⟩
  | fuel, .nonNull inner, source =>
      let child :=
        (RecordedExecution.completeValue schema resolvers variables fuel inner fields
          source path usages context allowStream (route ++ [0])).run
          supply
      (streamValue schema resolvers variables fuel inner fields source path usages context
        allowStream (route ++ [0]) supply).nonNull
        route child.1.report
  | fuel + 1, .list inner, .list sources =>
      listWithStream schema resolvers variables fuel inner fields sources path usages
        context allowStream (route ++ [0]) supply
  | _, _, _ => ⟨[], []⟩
termination_by (fuel, 1, sizeOf fieldType, 0)

end LiteralCuts

attribute [local simp] id_pure_eq id_bind_eq id_map_eq run_bind run_map

theorem literal_value_cut_accounting (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues) (fuel : Nat) (fieldType : TypeRef)
    (fields : List FieldDetails) (source : ResolverValue ObjectRef) (path : ResponsePath)
    (usages : List Nat) (context : DeferMap) (allowStream : Bool) (route : List Nat)
    (supply : Nat) (literal : LiteralValue source)
    : StreamCutAccounting
        ((RecordedExecution.completeValue schema resolvers variables fuel fieldType fields
            source path usages context allowStream route).run
          supply).1
        ((EagerRecordedExecution.completeValue schema resolvers variables fuel fieldType
            fields source path usages context allowStream route).run
          supply).1
        (LiteralCuts.streamValue schema resolvers variables fuel fieldType fields source
          path usages context allowStream route supply) := by
  cases fuel with
  | zero =>
      simp only [RecordedExecution.completeValue, EagerRecordedExecution.completeValue,
        LiteralCuts.streamValue, StateT.run_pure, id_pure_eq, StreamCutAccounting,
        RecordedCompletion.fault]
      exact ⟨ReportCutAccounting.refl _ (Scoped.primitive route 1).unique, .vacant .empty .empty⟩
  | succ fuel =>
      cases fieldType with
      | nonNull inner =>
          have child := literal_value_cut_accounting schema resolvers variables (fuel + 1) inner
            fields source path usages context allowStream (route ++ [0]) supply literal
          simpa only [RecordedExecution.completeValue,
            EagerRecordedExecution.completeValue, LiteralCuts.streamValue, run_bind,
            StateT.run_pure, id_pure_eq]
            using child.nonNull route
      | named name =>
          cases literal with
          | null =>
              simp only [RecordedExecution.completeValue, EagerRecordedExecution.completeValue,
                LiteralCuts.streamValue, StateT.run_pure, id_pure_eq, StreamCutAccounting,
                RecordedCompletion.pure]
              exact ⟨
                ReportCutAccounting.refl _ (by simp [Report.pure]),
                .vacant .empty .empty
              ⟩
          | scalar scalar =>
              simp only [RecordedExecution.completeValue, EagerRecordedExecution.completeValue,
                LiteralCuts.streamValue]
              split
              · exact ⟨ReportCutAccounting.refl _ (Scoped.primitive route 1).unique, .vacant .empty .empty⟩
              · exact ⟨ReportCutAccounting.refl _ (by simp [RecordedCompletion.pure, Report.pure]),
                  .vacant .empty .empty⟩
          | list sources =>
              simp only [RecordedExecution.completeValue, EagerRecordedExecution.completeValue,
                LiteralCuts.streamValue, StateT.run_pure, id_pure_eq, StreamCutAccounting,
                RecordedCompletion.fault]
              exact ⟨ReportCutAccounting.refl _ (Scoped.primitive route 1).unique, .vacant .empty .empty⟩
      | list inner =>
          cases literal with
          | null =>
              simp only [RecordedExecution.completeValue, EagerRecordedExecution.completeValue,
                LiteralCuts.streamValue, StateT.run_pure, id_pure_eq, StreamCutAccounting,
                RecordedCompletion.pure]
              exact ⟨
                ReportCutAccounting.refl _ (by simp [Report.pure]),
                .vacant .empty .empty
              ⟩
          | scalar scalar =>
              simp only [RecordedExecution.completeValue, EagerRecordedExecution.completeValue,
                LiteralCuts.streamValue, StateT.run_pure, id_pure_eq, StreamCutAccounting,
                RecordedCompletion.fault]
              exact ⟨ReportCutAccounting.refl _ (Scoped.primitive route 1).unique, .vacant .empty .empty⟩
          | @list sources known =>
              simpa only [RecordedExecution.completeValue, EagerRecordedExecution.completeValue,
                LiteralCuts.streamValue] using literal_listWithStream_cut_accounting schema resolvers
                  variables fuel inner fields sources path usages context allowStream (route ++ [0])
                  supply known
termination_by (fuel, 1, sizeOf fieldType, 0)
decreasing_by
  all_goals subst_vars; simp_wf
  all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right

/-- All finite actual literal value runs construct retained-scope cut accounting,
origin coverage and the same final supply. No comparison outputs or cut predicates are assumed. -/
def LiteralValueCutAccounting : Prop :=
  ∀ (ObjectRef : Type) (schema : Schema) (resolvers : Resolvers ObjectRef) variables fuel
    fieldType fields (source : ResolverValue ObjectRef) path usages context allowStream
    route supply,
    LiteralValue source
    → let cut :=
        (RecordedExecution.completeValue schema resolvers variables fuel fieldType fields
          source path usages context allowStream route).run
          supply
      let eager :=
        (EagerRecordedExecution.completeValue schema resolvers variables fuel fieldType
          fields source path usages context allowStream route).run
          supply
      let inventory :=
        LiteralCuts.streamValue schema resolvers variables fuel fieldType fields source
          path usages context allowStream route supply
      StreamCutAccounting cut.1 eager.1 inventory
      ∧ CompletionOriginsRefine cut.1 eager.1
      ∧ cut.2 = eager.2

theorem literalValueCutAccounting_holds : LiteralValueCutAccounting := by
  intro ObjectRef schema resolvers variables fuel fieldType fields source path usages context allowStream
    route supply literal
  exact ⟨literal_value_cut_accounting schema resolvers variables fuel fieldType fields source path usages
    context allowStream route supply literal,
    literalOriginsConstruction_holds ObjectRef schema resolvers variables fuel fieldType fields source path
      usages context allowStream route literal supply⟩

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.OriginAccounting
