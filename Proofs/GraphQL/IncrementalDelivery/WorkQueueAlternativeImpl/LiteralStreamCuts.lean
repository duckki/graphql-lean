import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.LiteralReachedCuts
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.LiteralEmptyWork

/-! Origin accounting at each actual retained literal stream-item report. One
ordered inventory records the nested sibling cuts of exactly those items retained by
the cut executor. The fatal stream stop is shared with eager execution and does not
explain additional omissions. Pure future reports are not native recording events. -/

namespace
  GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.OriginAccounting

open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Semantics
open ScheduledWork (LiteralValue)

namespace LiteralCuts

/-- One entry per actual retained item. The shared fatal stop does not add a cut
cone: neither executor retains reports for the suffix after that item. -/
def streamItems (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues) (fuel : Nat) (itemType : TypeRef)
    (fields : List FieldDetails) (sources : List (ResolverValue ObjectRef))
    (path : ResponsePath) (index : Nat) (route : List Nat) (supply : Nat)
    : List (List SiblingCut) :=
  match sources with
  | [] => []
  | source :: rest =>
      let head :=
        (RecordedExecution.completeValue schema resolvers variables fuel itemType
          fields source (path ++ [.index index]) [] [] false (route ++ [0])).run
          supply
      let sites :=
        value schema resolvers variables fuel itemType fields source
          (path ++ [.index index]) [] [] (route ++ [0]) supply
      match head.1.report.outcome with
      | .error _ => [sites]
      | .ok _ =>
          sites
          :: streamItems schema resolvers variables fuel itemType fields rest
              path (index + 1) (route ++ [1]) head.2

end LiteralCuts

/-- Constructed report identity, reached-cut explanation and exact count gap at
one scope. None of these facts claims native recording times or error-object association. -/
def ReportCutAccounting (cut eager : Report α) (sites : List SiblingCut) : Prop :=
  ReportRefines cut eager
  ∧ OmissionAtCuts ⟨cut, .empty, none⟩ ⟨eager, .empty, none⟩ sites
  ∧ eager.origins.Nodup
  ∧ ScheduledErrors.countedErrors cut.outcome
      + (omittedOrigins cut.origins eager.origins).length
    = ScheduledErrors.countedErrors eager.outcome

theorem literal_report_cut_accounting (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues) (fuel : Nat) (fieldType : TypeRef)
    (fields : List FieldDetails) (source : ResolverValue ObjectRef) (path : ResponsePath)
    (usages : List Nat) (context : DeferMap) (route : List Nat) (supply : Nat)
    (literal : LiteralValue source)
    : ReportCutAccounting
        ((RecordedExecution.completeValue schema resolvers variables fuel fieldType fields
            source path usages context false route).run
          supply).1.report
        ((EagerRecordedExecution.completeValue schema resolvers variables fuel fieldType
            fields source path usages context false route).run
          supply).1.report
        (LiteralCuts.value schema resolvers variables fuel fieldType fields source path
          usages context route supply) := by
  obtain ⟨coverage, omitted, gap⟩ := literalReachedCutAccounting_holds ObjectRef schema resolvers
    variables fuel fieldType fields source path usages context route supply literal
  exact ⟨coverage.1, omitted,
    (EagerScopes.completeValue_origins schema resolvers variables fuel fieldType fields source
      path usages context false route supply).left.unique, gap⟩

/-- The same ordered positions and one preselected cut inventory, including the
fatal item if present. Children remain actual Work, not flattened into the item count. -/
inductive ItemCutAccounting
    : List (RecordedOutcome ResponseValue × RecordedWork)
      → List (RecordedOutcome ResponseValue × RecordedWork) → List (List SiblingCut)
      → Prop where
  | nil : ItemCutAccounting [] [] []
  | cons {cut eager children eagerChildren rest eagerRest sites remaining}
    (head : ReportCutAccounting cut.toReport eager.toReport sites)
    (cutChildren : EmptyRecordedWork children)
    (eagerVacant : EmptyRecordedWork eagerChildren)
    (tail : ItemCutAccounting rest eagerRest remaining)
    : ItemCutAccounting ((cut, children) :: rest) ((eager, eagerChildren) :: eagerRest)
        (sites :: remaining)

def ItemCutAccounting.AtIndex
    (cut eager : List (RecordedOutcome ResponseValue × RecordedWork))
    (sites : List (List SiblingCut)) (index : Nat)
    : Prop :=
  match cut[index]?, eager[index]?, sites[index]? with
  | none, none, none => True
  | some before, some after, some cuts =>
      ReportCutAccounting before.1.toReport after.1.toReport cuts
      ∧ EmptyRecordedWork before.2
      ∧ EmptyRecordedWork after.2
  | _, _, _ => False

theorem ItemCutAccounting.atIndex {cut eager sites}
    (known : ItemCutAccounting cut eager sites) (index : Nat)
    : ItemCutAccounting.AtIndex cut eager sites index := by
  induction index generalizing cut eager sites with
  | zero =>
      cases known with
      | nil => trivial
      | cons head before after tail => exact ⟨head, before, after⟩
  | succ index ih =>
      cases known with
      | nil => trivial
      | cons head before after tail => exact ih tail

theorem ItemCutAccounting.lengths {cut eager sites}
    (known : ItemCutAccounting cut eager sites)
    : cut.length = eager.length ∧ cut.length = sites.length := by
  induction known with
  | nil => exact ⟨rfl, rfl⟩
  | cons head before after tail ih =>
      simpa only [List.length_cons, Nat.add_right_cancel_iff] using ih

/-- Empty child Work closes the coverage boundary: every omitted retained-tail
origin belongs to one of the same preselected per-item cut inventories. -/
theorem ItemCutAccounting.omitted_origins {cut eager sites}
    (known : ItemCutAccounting cut eager sites)
    : ∀ origin ∈ omittedOrigins (itemOrigins cut) (itemOrigins eager),
        WithinCuts sites.flatten origin := by
  induction known with
  | nil =>
      intro origin missing
      exact False.elim (List.not_mem_nil missing)
  | cons head before after tail ih =>
      intro origin missing
      simp only [itemOrigins, List.flatMap_cons, before.origins, after.origins,
        List.append_nil] at missing
      rcases append_omitted_within head.2.1.1 ih origin missing with earlier | later
      · exact WithinCuts.left earlier
      · exact WithinCuts.right later

theorem ItemCutAccounting.cuts_positive {cut eager sites}
    (known : ItemCutAccounting cut eager sites)
    : ∀ site ∈ sites.flatten, 0 < site.errors := by
  induction known with
  | nil => simp
  | cons head before after tail ih =>
      intro site member
      rcases List.mem_append.mp member with earlier | later
      · exact head.2.1.2 site earlier
      · exact ih site later

attribute [local simp] id_pure_eq id_bind_eq id_map_eq run_bind run_map

theorem literal_streamItems_cut_accounting (schema : Schema)
    (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
    (itemType : TypeRef) (fields : List FieldDetails)
    (sources : List (ResolverValue ObjectRef)) (path : ResponsePath) (index : Nat)
    (route : List Nat) (supply : Nat) (literal : ∀ source ∈ sources, LiteralValue source)
    : ItemCutAccounting
        ((RecordedExecution.completeStreamItems schema resolvers variables fuel itemType
            fields sources path index route).run
          supply).1
        ((EagerRecordedExecution.completeStreamItems schema resolvers variables fuel
            itemType fields sources path index route).run
          supply).1
        (LiteralCuts.streamItems schema resolvers variables fuel itemType fields sources
          path index route supply) := by
  induction sources generalizing index route with
  | nil =>
      simpa only [RecordedExecution.completeStreamItems,
        EagerRecordedExecution.completeStreamItems, LiteralCuts.streamItems, StateT.run_pure,
        id_pure_eq] using ItemCutAccounting.nil
  | cons source rest ih =>
      obtain ⟨related, headSupply, eagerHeadSupply⟩ := literal_completeValue_origins schema resolvers
        variables fuel itemType fields source (path ++ [.index index]) [] [] (route ++ [0])
        (literal source (by simp)) supply
      have head := literal_report_cut_accounting schema resolvers variables fuel itemType fields
        source (path ++ [.index index]) [] [] (route ++ [0]) supply (literal source (by simp))
      have tail := ih (index + 1) (route ++ [1])
        (fun source member => literal source (List.mem_cons_of_mem _ member))
      obtain ⟨cutChildren, eagerChildren⟩ := literal_value_emptyWork schema resolvers variables fuel
        itemType fields source (path ++ [.index index]) [] [] (route ++ [0]) supply
        (literal source (by simp))
      have same := related.1.1.1
      simp only [RecordedExecution.completeStreamItems, EagerRecordedExecution.completeStreamItems,
        LiteralCuts.streamItems, run_bind, headSupply, eagerHeadSupply]
      cases outcome :
          ((RecordedExecution.completeValue schema resolvers variables fuel itemType fields source
            (path ++ [.index index]) [] [] false (route ++ [0])).run supply).1.report.outcome
      <;> cases eagerOutcome :
          ((EagerRecordedExecution.completeValue schema resolvers variables fuel itemType fields source
            (path ++ [.index index]) [] [] false (route ++ [0])).run supply).1.report.outcome
      <;> simp only [ScheduledErrors.SameData, outcome, eagerOutcome] at same
      · simp only [StateT.run_pure, id_pure_eq]
        exact .cons head .empty .empty .nil
      · simp only [run_bind, StateT.run_pure, id_pure_eq]
        exact .cons head cutChildren eagerChildren tail

/-- Actual retained literal stream reports construct their ordered cut inventory
and every report's identity/count accounting; no matching outputs or cuts are premises. -/
def LiteralStreamTailAccounting : Prop :=
  ∀ (ObjectRef : Type) (schema : Schema) (resolvers : Resolvers ObjectRef) variables fuel
    itemType fields (sources : List (ResolverValue ObjectRef)) path index route supply,
    (∀ source ∈ sources, LiteralValue source)
    → ItemCutAccounting
        ((RecordedExecution.completeStreamItems schema resolvers variables fuel itemType
            fields sources path index route).run
          supply).1
        ((EagerRecordedExecution.completeStreamItems schema resolvers variables fuel
            itemType fields sources path index route).run
          supply).1
        (LiteralCuts.streamItems schema resolvers variables fuel itemType fields sources
          path index route supply)

theorem literalStreamTailAccounting_holds : LiteralStreamTailAccounting := by
  intro ObjectRef schema resolvers variables fuel itemType fields sources path index route supply literal
  exact literal_streamItems_cut_accounting schema resolvers variables fuel itemType fields sources
    path index route supply literal

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.OriginAccounting
