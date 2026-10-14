import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.LiteralStreamCuts

/-! Constructed initial/tail cut accounting for an actual literal outer stream.
The one inventory is selected by actual control flow before observing any origin
or item index. Empty and suppressed boundaries remain distinct. Nothing here turns
pure retained reports into native error-recording events. -/

namespace
  GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.OriginAccounting

open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Semantics
open ScheduledWork (LiteralValue)

structure StreamCutInventory where
  initial : List SiblingCut
  items : List (List SiblingCut)
deriving Repr

def StreamCutInventory.sites (inventory : StreamCutInventory) : List SiblingCut :=
  inventory.initial ++ inventory.items.flatten

namespace LiteralCuts

/-- Inspect initial execution before deciding whether the actual stream boundary
exists. A shared fatal stream stop is not another omission site. -/
def listWithStream (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues) (fuel : Nat) (itemType : TypeRef)
    (fields : List FieldDetails) (sources : List (ResolverValue ObjectRef))
    (path : ResponsePath) (usages : List Nat) (context : DeferMap) (allowStream : Bool)
    (route : List Nat) (supply : Nat)
    : StreamCutInventory :=
  match (if allowStream then
            getStreamUsage variables (fields.head?.map FieldDetails.directives |>.getD [])
          else
            .ok none) with
  | .error _ => ⟨[], []⟩
  | .ok none =>
      ⟨
        items schema resolvers variables fuel itemType fields sources path 0 usages
          context (route ++ [0]) supply,
        []
      ⟩
  | .ok (some usage) =>
      let initial :=
        (RecordedExecution.completeListValue schema resolvers variables fuel
          itemType fields (sources.take usage.initialCount) path 0 usages context
          (route ++ [0])).run
          supply
      let sites :=
        items schema resolvers variables fuel itemType fields
          (sources.take usage.initialCount) path 0 usages context (route ++ [0]) supply
      match initial.1.report.outcome with
      | .error _ => ⟨sites, []⟩
      | .ok _ =>
          if sources.length < usage.initialCount then
            ⟨sites, []⟩
          else
            ⟨
              sites,
              streamItems schema resolvers variables fuel itemType
                (fields.map (fun field => { field with deferUsage := none }))
                (sources.drop usage.initialCount) path usage.initialCount (route ++ [1])
                (initial.2 + 1)
            ⟩

end LiteralCuts

theorem ReportCutAccounting.refl (report : Report α) (unique : report.origins.Nodup)
    : ReportCutAccounting report report [] := by
  refine ⟨ReportRefines.refl _, ?_, unique, (ReportRefines.refl _).omitted_count unique⟩
  simp [OmissionAtCuts, omittedOrigins_self]

theorem ReportCutAccounting.catchNull (wrap : α → ResponseValue) {cut eager : Report α}
    {sites} (known : ReportCutAccounting cut eager sites)
    : ReportCutAccounting (cut.catchNull wrap) (eager.catchNull wrap) sites :=
  ⟨
    known.1.catchNull wrap,
    known.2.1,
    known.2.2.1,
    (known.1.catchNull wrap).omitted_count known.2.2.1
  ⟩

theorem literal_list_report_cut_accounting (schema : Schema)
    (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
    (itemType : TypeRef) (fields : List FieldDetails)
    (sources : List (ResolverValue ObjectRef)) (path : ResponsePath) (index : Nat)
    (usages : List Nat) (context : DeferMap) (route : List Nat) (supply : Nat)
    (literal : ∀ source ∈ sources, LiteralValue source)
    : ReportCutAccounting
        ((RecordedExecution.completeListValue schema resolvers variables fuel itemType
            fields sources path index usages context route).run
          supply).1.report
        ((EagerRecordedExecution.completeListValue schema resolvers variables fuel
            itemType fields sources path index usages context route).run
          supply).1.report
        (LiteralCuts.items schema resolvers variables fuel itemType fields sources path
          index usages context route supply) := by
  have related := (literal_completeListValue_origins schema resolvers variables fuel itemType fields
    sources path index usages context route literal supply).1.1
  have unique := (EagerScopes.completeListValue_origins schema resolvers variables fuel itemType fields
    sources path index usages context route supply).left.unique
  exact ⟨related, literal_items_omission schema resolvers variables fuel itemType fields sources path
    index usages context route supply literal, unique, related.omitted_count unique⟩

/-- Actual literal outer Work is either vacant or exactly the initial Work joined
with one stream boundary. An empty boundary still has the second constructor. -/
inductive LiteralStreamWorkAccounting
    : RecordedWork → RecordedWork → List (List SiblingCut) → Prop where
  | vacant {cut eager} (before : EmptyRecordedWork cut) (after : EmptyRecordedWork eager)
    : LiteralStreamWorkAccounting cut eager []
  | stream {cut eager node eagerNode items eagerItems sites}
    (before : EmptyRecordedWork cut) (after : EmptyRecordedWork eager)
    (tail : ItemCutAccounting items eagerItems sites)
    : LiteralStreamWorkAccounting (.combine cut (.stream node items))
        (.combine eager (.stream eagerNode eagerItems)) sites

theorem LiteralStreamWorkAccounting.omitted_origins {cut eager sites}
    (known : LiteralStreamWorkAccounting cut eager sites)
    : ∀ origin ∈ omittedOrigins cut.origins eager.origins,
        WithinCuts sites.flatten origin := by
  cases known with
  | vacant before after =>
      simp only [before.origins, after.origins, omittedOrigins_self, List.not_mem_nil]
      intro origin missing
      exact False.elim missing
  | stream before after tail =>
      simpa only [RecordedWork.origins, before.origins, after.origins, List.nil_append,
        itemOrigins] using tail.omitted_origins

theorem LiteralStreamWorkAccounting.cuts_positive {cut eager sites}
    (known : LiteralStreamWorkAccounting cut eager sites)
    : ∀ site ∈ sites.flatten, 0 < site.errors := by
  cases known with
  | vacant before after => simp
  | stream before after tail => exact tail.cuts_positive

def StreamCutAccounting (cut eager : RecordedCompletion ResponseValue)
    (inventory : StreamCutInventory)
    : Prop :=
  ReportCutAccounting cut.report eager.report inventory.initial
  ∧ LiteralStreamWorkAccounting cut.work eager.work inventory.items

/-- All retained initial and future origins are covered by one actual inventory.
This combines scope inventories, not initial-response error counts or native times. -/
theorem StreamCutAccounting.omitted_origins {cut eager inventory}
    (known : StreamCutAccounting cut eager inventory)
    : ∀ origin ∈ omittedOrigins cut.origins eager.origins,
        WithinCuts inventory.sites origin := by
  intro origin missing
  rcases append_omitted_within known.1.2.1.1 known.2.omitted_origins origin missing
    with initial | future
  · exact initial.left
  · exact future.right

theorem StreamCutAccounting.cuts_positive {cut eager inventory}
    (known : StreamCutAccounting cut eager inventory)
    : ∀ site ∈ inventory.sites, 0 < site.errors := by
  intro site member
  rcases List.mem_append.mp member with initial | future
  · exact known.1.2.1.2 site initial
  · exact known.2.cuts_positive site future

attribute [local simp] id_pure_eq id_bind_eq id_map_eq run_bind run_map

theorem literal_listWithStream_cut_accounting (schema : Schema)
    (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
    (itemType : TypeRef) (fields : List FieldDetails)
    (sources : List (ResolverValue ObjectRef)) (path : ResponsePath) (usages : List Nat)
    (context : DeferMap) (allowStream : Bool) (route : List Nat) (supply : Nat)
    (literal : ∀ source ∈ sources, LiteralValue source)
    : StreamCutAccounting
        ((RecordedExecution.completeListValueWithStream schema resolvers variables fuel
            itemType fields sources path usages context allowStream route).run
          supply).1
        ((EagerRecordedExecution.completeListValueWithStream schema resolvers variables
            fuel itemType fields sources path usages context allowStream route).run
          supply).1
        (LiteralCuts.listWithStream schema resolvers variables fuel itemType fields
          sources path usages context allowStream route supply) := by
  cases usageResult
        : (if allowStream then
              getStreamUsage variables
                (fields.head?.map FieldDetails.directives |>.getD [])
            else
              .ok none) with
  | error errors =>
      simp only [RecordedExecution.completeListValueWithStream,
        EagerRecordedExecution.completeListValueWithStream, LiteralCuts.listWithStream, usageResult,
        StateT.run_pure, id_pure_eq, StreamCutAccounting, RecordedCompletion.fault]
      exact ⟨ReportCutAccounting.refl _ (Scoped.primitive route errors).unique,
        .vacant .empty .empty⟩
  | ok option =>
      cases option with
      | none =>
          have report := (literal_list_report_cut_accounting schema resolvers variables fuel itemType
            fields sources path 0 usages context (route ++ [0]) supply literal).catchNull ResponseValue.list
          obtain ⟨before, after⟩ := literal_items_emptyWork schema resolvers variables fuel itemType
            fields sources path 0 usages context (route ++ [0]) supply literal
          simpa only [RecordedExecution.completeListValueWithStream,
            EagerRecordedExecution.completeListValueWithStream,
            LiteralCuts.listWithStream, usageResult, run_bind, StateT.run_pure,
            id_pure_eq, StreamCutAccounting, RecordedCompletion.catchNull]
            using And.intro report
              (LiteralStreamWorkAccounting.vacant (before.catchNull ResponseValue.list)
                (after.catchNull ResponseValue.list))
      | some usage =>
          have initialLiteral : ∀ source ∈ sources.take usage.initialCount, LiteralValue source :=
            fun source member => literal source (List.mem_of_mem_take member)
          obtain ⟨related, initialSupply, eagerInitialSupply⟩ := literal_completeListValue_origins schema
            resolvers variables fuel itemType fields (sources.take usage.initialCount) path 0 usages
            context (route ++ [0]) initialLiteral supply
          have report := (literal_list_report_cut_accounting schema resolvers variables fuel itemType
            fields (sources.take usage.initialCount) path 0 usages context (route ++ [0]) supply
            initialLiteral).catchNull ResponseValue.list
          obtain ⟨before, after⟩ := literal_items_emptyWork schema resolvers variables fuel itemType
            fields (sources.take usage.initialCount) path 0 usages context (route ++ [0]) supply initialLiteral
          have same := related.1.1.1
          simp only [RecordedExecution.completeListValueWithStream,
            EagerRecordedExecution.completeListValueWithStream, LiteralCuts.listWithStream, usageResult,
            run_bind, initialSupply, eagerInitialSupply]
          cases outcome : ((RecordedExecution.completeListValue schema resolvers variables fuel itemType
              fields (sources.take usage.initialCount) path 0 usages context (route ++ [0])).run
              supply).1.report.outcome
          <;> cases eagerOutcome : ((EagerRecordedExecution.completeListValue schema resolvers variables fuel
              itemType fields (sources.take usage.initialCount) path 0 usages context (route ++ [0])).run
              supply).1.report.outcome
          <;> simp only [ScheduledErrors.SameData, outcome, eagerOutcome] at same
          · simp only [StateT.run_pure, id_pure_eq, StreamCutAccounting]
            exact ⟨report, .vacant (before.catchNull ResponseValue.list) (after.catchNull ResponseValue.list)⟩
          · simp only
            split
            · simp only [StateT.run_pure, id_pure_eq, StreamCutAccounting]
              exact ⟨report, .vacant (before.catchNull ResponseValue.list) (after.catchNull ResponseValue.list)⟩
            · have tail := literal_streamItems_cut_accounting schema resolvers variables fuel itemType
                (fields.map (fun field => { field with deferUsage := none }))
                (sources.drop usage.initialCount) path usage.initialCount (route ++ [1]) (supply + 1)
                (fun source member => literal source (List.mem_of_mem_drop member))
              simp only [freshNodeRef, run_bind, StateT.run_get, StateT.run_set,
                StateT.run_pure, id_pure_eq, StreamCutAccounting]
              exact ⟨report, .stream (before.catchNull ResponseValue.list)
                (after.catchNull ResponseValue.list) tail⟩

/-- One actual outer-stream comparison supplies all retained-scope accounting and
the existing full origin/supply correspondence. No desired output or cut trace is a premise. -/
def LiteralStreamAccounting : Prop :=
  ∀ (ObjectRef : Type) (schema : Schema) (resolvers : Resolvers ObjectRef) variables fuel
    itemType fields (sources : List (ResolverValue ObjectRef)) path usages context
    allowStream route supply,
    (∀ source ∈ sources, LiteralValue source)
    → let cut :=
        (RecordedExecution.completeListValueWithStream schema resolvers variables fuel
          itemType fields sources path usages context allowStream route).run
          supply
      let eager :=
        (EagerRecordedExecution.completeListValueWithStream schema resolvers variables
          fuel itemType fields sources path usages context allowStream route).run
          supply
      let inventory :=
        LiteralCuts.listWithStream schema resolvers variables fuel itemType fields sources
          path usages context allowStream route supply
      StreamCutAccounting cut.1 eager.1 inventory
      ∧ CompletionOriginsRefine cut.1 eager.1
      ∧ cut.2 = eager.2

theorem literalStreamAccounting_holds : LiteralStreamAccounting := by
  intro ObjectRef schema resolvers variables fuel itemType fields sources path usages context allowStream
    route supply literal
  exact ⟨literal_listWithStream_cut_accounting schema resolvers variables fuel itemType fields sources path
    usages context allowStream route supply literal,
    literal_completeListValueWithStream_origins schema resolvers variables fuel itemType fields sources
      path usages context allowStream route literal supply⟩

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.OriginAccounting
