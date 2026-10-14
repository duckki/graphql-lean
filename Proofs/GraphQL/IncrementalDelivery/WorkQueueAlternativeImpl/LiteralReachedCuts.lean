import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.LiteralOriginConstruction
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.OriginOmissions
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.EagerOriginUniqueness

/-! Reached sibling cuts of actual nonstreaming literal completion. A site is added
only when the actual annotated head returns a fatal outcome. This is a finite pure
execution witness, not evidence of native cancellation or absence of early records. -/

namespace
  GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.OriginAccounting

open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Semantics
open ScheduledWork (LiteralValue)

structure SiblingCut where
  tailRoute : List Nat
  errors : Nat
deriving Repr, DecidableEq

def WithinCuts (cuts : List SiblingCut) (origin : Origin) : Prop :=
  ∃ site ∈ cuts, site.tailRoute.IsPrefix origin.1

theorem WithinCuts.left {cuts rest : List SiblingCut} {origin : Origin}
    (known : WithinCuts cuts origin)
    : WithinCuts (cuts ++ rest) origin := by
  obtain ⟨site, member, inside⟩ := known
  exact ⟨site, List.mem_append_left _ member, inside⟩

theorem WithinCuts.right {cuts rest : List SiblingCut} {origin : Origin}
    (known : WithinCuts rest origin)
    : WithinCuts (cuts ++ rest) origin := by
  obtain ⟨site, member, inside⟩ := known
  exact ⟨site, List.mem_append_right _ member, inside⟩

namespace LiteralCuts

mutual
  /-- Inspect only recursive calls reached by the actual cut policy. Objects are
  outside this witness's theorem domain and contribute no sites here. -/
  def value (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variables : VariableValues) (fuel : Nat) (fieldType : TypeRef)
      (fields : List FieldDetails) (source : ResolverValue ObjectRef)
      (path : ResponsePath) (usages : List Nat) (context : DeferMap) (route : List Nat)
      (supply : Nat)
      : List SiblingCut :=
    match fuel, fieldType, source with
    | 0, _, _ => []
    | fuel, .nonNull inner, source =>
        value schema resolvers variables fuel inner fields source path usages context
          (route ++ [0]) supply
    | fuel + 1, .list inner, .list sources =>
        items schema resolvers variables fuel inner fields sources path 0 usages context
          (route ++ [0] ++ [0]) supply
    | _, _, _ => []
  termination_by (fuel, 1, sizeOf fieldType, 0)

  def items (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variables : VariableValues) (fuel : Nat) (itemType : TypeRef)
      (fields : List FieldDetails) (sources : List (ResolverValue ObjectRef))
      (path : ResponsePath) (index : Nat) (usages : List Nat) (context : DeferMap)
      (route : List Nat) (supply : Nat)
      : List SiblingCut :=
    match sources with
    | [] => []
    | source :: rest =>
        let head :=
          (RecordedExecution.completeValue schema resolvers variables fuel itemType fields
            source (path ++ [.index index]) usages context false (route ++ [0])).run
            supply
        let nested :=
          value schema resolvers variables fuel itemType fields source
            (path ++ [.index index]) usages context (route ++ [0]) supply
        match head.1.report.outcome with
        | .error errors => nested ++ [{ tailRoute := route ++ [1], errors }]
        | .ok _ =>
            nested
            ++ items schema resolvers variables fuel itemType fields rest
                path (index + 1) usages context (route ++ [1]) head.2
  termination_by (fuel, 2, sizeOf itemType, sizeOf sources)
end

end LiteralCuts

attribute [local simp] id_pure_eq id_bind_eq id_map_eq run_bind run_map

theorem RecordedCompletion.combine_report (f : α → β → γ)
    (left : RecordedCompletion α) (right : RecordedCompletion β)
    : (RecordedCompletion.combine f left right).report
      = Report.combine f left.report right.report := by
  simp only [RecordedCompletion.combine]
  split <;> rfl

def OmissionAtCuts (cut eager : RecordedCompletion α) (cuts : List SiblingCut) : Prop :=
  (∀ origin ∈ omittedOrigins cut.report.origins eager.report.origins,
    WithinCuts cuts origin)
  ∧ ∀ site ∈ cuts, 0 < site.errors

mutual
  theorem literal_value_omission (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variables : VariableValues) (fuel : Nat) (fieldType : TypeRef)
      (fields : List FieldDetails) (source : ResolverValue ObjectRef)
      (path : ResponsePath) (usages : List Nat) (context : DeferMap) (route : List Nat)
      (supply : Nat) (literal : LiteralValue source)
      : OmissionAtCuts
          ((RecordedExecution.completeValue schema resolvers variables fuel fieldType
              fields source path usages context false route).run
            supply).1
          ((EagerRecordedExecution.completeValue schema resolvers variables fuel fieldType
              fields source path usages context false route).run
            supply).1
          (LiteralCuts.value schema resolvers variables fuel fieldType fields source path
            usages context route supply) := by
    cases fuel with
    | zero => simp [OmissionAtCuts, RecordedExecution.completeValue,
        EagerRecordedExecution.completeValue, LiteralCuts.value, omittedOrigins_self]
    | succ fuel =>
        cases fieldType with
        | nonNull inner =>
            have child := literal_value_omission schema resolvers variables (fuel + 1) inner
              fields source path usages context (route ++ [0]) supply literal
            have related := (literal_completeValue_origins schema resolvers variables (fuel + 1)
              inner fields source path usages context (route ++ [0]) literal supply).1.1
            simpa only [RecordedExecution.completeValue,
              EagerRecordedExecution.completeValue, LiteralCuts.value, run_bind,
              StateT.run_pure, id_pure_eq, RecordedCompletion.nonNull,
              related.nonNull_omitted route, OmissionAtCuts]
              using child
        | named name =>
            cases literal with
            | null =>
                simp [OmissionAtCuts, RecordedExecution.completeValue,
                  EagerRecordedExecution.completeValue, LiteralCuts.value, omittedOrigins_self]
            | scalar scalar =>
                simp only [RecordedExecution.completeValue, EagerRecordedExecution.completeValue]
                split <;> simp [OmissionAtCuts, LiteralCuts.value, omittedOrigins_self]
            | list sources =>
                simp [OmissionAtCuts, RecordedExecution.completeValue,
                  EagerRecordedExecution.completeValue, LiteralCuts.value, omittedOrigins_self]
        | list inner =>
            cases literal with
            | null =>
                simp [OmissionAtCuts, RecordedExecution.completeValue,
                  EagerRecordedExecution.completeValue, LiteralCuts.value, omittedOrigins_self]
            | scalar scalar =>
                simp [OmissionAtCuts, RecordedExecution.completeValue,
                  EagerRecordedExecution.completeValue, LiteralCuts.value, omittedOrigins_self]
            | @list sources known =>
                have child := literal_items_omission schema resolvers variables fuel inner
                  fields sources path 0 usages context (route ++ [0] ++ [0]) supply known
                simpa only [OmissionAtCuts, RecordedExecution.completeValue,
                  EagerRecordedExecution.completeValue, RecordedExecution.completeListValueWithStream,
                  EagerRecordedExecution.completeListValueWithStream, Bool.false_eq_true,
                  ↓reduceIte, LiteralCuts.value, run_bind, StateT.run_pure, id_pure_eq,
                  RecordedCompletion.catchNull, Report.catchNull] using child
  termination_by (fuel, 1, sizeOf fieldType, 0)
  decreasing_by
    all_goals subst_vars; simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right

  theorem literal_items_omission (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variables : VariableValues) (fuel : Nat) (itemType : TypeRef)
      (fields : List FieldDetails) (sources : List (ResolverValue ObjectRef))
      (path : ResponsePath) (index : Nat) (usages : List Nat) (context : DeferMap)
      (route : List Nat) (supply : Nat)
      (literal : ∀ source ∈ sources, LiteralValue source)
      : OmissionAtCuts
          ((RecordedExecution.completeListValue schema resolvers variables fuel itemType
              fields sources path index usages context route).run
            supply).1
          ((EagerRecordedExecution.completeListValue schema resolvers variables fuel
              itemType fields sources path index usages context route).run
            supply).1
          (LiteralCuts.items schema resolvers variables fuel itemType fields sources path
            index usages context route supply) := by
    cases sources with
    | nil => simp [OmissionAtCuts, RecordedExecution.completeListValue,
        EagerRecordedExecution.completeListValue, LiteralCuts.items, omittedOrigins_self]
    | cons source rest =>
        have head := literal_value_omission schema resolvers variables fuel itemType fields
          source (path ++ [.index index]) usages context (route ++ [0]) supply
          (literal source (by simp))
        have tail := literal_items_omission schema resolvers variables fuel itemType fields
          rest path (index + 1) usages context (route ++ [1]) supply
          (fun source member => literal source (List.mem_cons_of_mem _ member))
        obtain ⟨related, headSupply, eagerHeadSupply⟩ :=
          literal_completeValue_origins schema resolvers variables fuel itemType fields source
            (path ++ [.index index]) usages context (route ++ [0]) (literal source (by simp)) supply
        simp only [OmissionAtCuts, RecordedExecution.completeListValue,
          EagerRecordedExecution.completeListValue, LiteralCuts.items, run_bind,
          headSupply, eagerHeadSupply]
        cases outcome
              : ((RecordedExecution.completeValue schema resolvers variables fuel itemType
                    fields source (path ++ [.index index]) usages context false
                    (route ++ [0])).run
                  supply).1.report.outcome with
        | error errors =>
            simp only [StateT.run_pure, id_pure_eq, RecordedCompletion.map, Report.map,
              RecordedCompletion.combine_report]
            have headScope := (completeValue_origins schema resolvers variables fuel itemType fields
              source (path ++ [.index index]) usages context false (route ++ [0]) supply).left
            have tailScope := (EagerScopes.completeListValue_origins schema resolvers variables fuel
              itemType fields rest path (index + 1) usages context (route ++ [1]) supply).left
            have omitted := fatal_cut_omitted_within List.cons (fun value => [value])
              (((EagerRecordedExecution.completeListValue schema resolvers variables fuel itemType
                fields rest path (index + 1) usages context (route ++ [1])).run supply).1.report)
              route headScope tailScope head.1
            have erased := congrArg (fun output => output.1.result)
              (completeValue_erases schema resolvers variables fuel itemType fields source
                (path ++ [.index index]) usages context false (route ++ [0]) supply)
            change _ = ((ScheduledExecution.completeValue schema resolvers variables fuel itemType
              fields source (path ++ [.index index]) usages context false).run supply).1.result at erased
            have positive := (ScheduledExecution.completeValue_positive schema resolvers variables fuel
              itemType fields source (path ++ [.index index]) usages context false supply).1
            rw [← erased] at positive
            refine ⟨?_, ?_⟩
            · intro origin member
              rcases omitted origin member with earlier | later
              · exact earlier.left
              · exact WithinCuts.right ⟨{ tailRoute := route ++ [1], errors }, by simp, later⟩
            · intro site member
              rcases List.mem_append.mp member with earlier | later
              · exact head.2 site earlier
              · obtain rfl := List.mem_singleton.mp later
                exact positive errors outcome
        | ok value =>
            simp only [run_bind, StateT.run_pure, id_pure_eq, RecordedCompletion.combine_report]
            have omitted := combine_omitted_within List.cons head.1 tail.1
            refine ⟨?_, ?_⟩
            · intro origin member
              rcases omitted origin member with earlier | later
              · exact earlier.left
              · exact later.right
            · intro site member
              rcases List.mem_append.mp member with earlier | later
              · exact head.2 site earlier
              · exact tail.2 site later
  termination_by (fuel, 2, sizeOf itemType, sizeOf sources)
  decreasing_by
    all_goals subst_vars; simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right
    all_goals try omega
end

/-- Every omitted actual literal report origin is inside a reached sibling cut;
every recorded cut has a positive actual fatal count. No cut trace is supplied. -/
def LiteralReachedCutOmission : Prop :=
  ∀ (ObjectRef : Type) (schema : Schema) (resolvers : Resolvers ObjectRef) variables fuel
    fieldType fields (source : ResolverValue ObjectRef) path usages context route supply,
    LiteralValue source
    → OmissionAtCuts
        ((RecordedExecution.completeValue schema resolvers variables fuel fieldType fields
            source path usages context false route).run
          supply).1
        ((EagerRecordedExecution.completeValue schema resolvers variables fuel fieldType
            fields source path usages context false route).run
          supply).1
        (LiteralCuts.value schema resolvers variables fuel fieldType fields source path
          usages context route supply)

theorem literalReachedCutOmission_holds : LiteralReachedCutOmission := by
  intro ObjectRef schema resolvers variables fuel fieldType fields source path usages context route supply
    literal
  exact literal_value_omission schema resolvers variables fuel fieldType fields source path usages context
    route supply literal

/-- One actual literal comparison constructs coverage, reached positive cuts and
the exact originating-reference count gap. This is not native recording evidence. -/
def LiteralReachedCutAccounting : Prop :=
  ∀ (ObjectRef : Type) (schema : Schema) (resolvers : Resolvers ObjectRef) variables fuel
    fieldType fields (source : ResolverValue ObjectRef) path usages context route supply,
    LiteralValue source
    → let cut :=
        (RecordedExecution.completeValue schema resolvers variables fuel fieldType fields
          source path usages context false route).run
          supply
      let eager :=
        (EagerRecordedExecution.completeValue schema resolvers variables fuel fieldType
          fields source path usages context false route).run
          supply
      let sites :=
        LiteralCuts.value schema resolvers variables fuel fieldType fields source path
          usages context route supply
      CompletionOriginsRefine cut.1 eager.1
      ∧ OmissionAtCuts cut.1 eager.1 sites
      ∧ ScheduledErrors.countedErrors cut.1.report.outcome
          + (omittedOrigins cut.1.report.origins eager.1.report.origins).length
        = ScheduledErrors.countedErrors eager.1.report.outcome

theorem literalReachedCutAccounting_holds : LiteralReachedCutAccounting := by
  intro ObjectRef schema resolvers variables fuel fieldType fields source path usages context route supply
    literal
  have coverage := (literal_completeValue_origins schema resolvers variables fuel fieldType fields
    source path usages context route literal supply).1
  have omitted := literalReachedCutOmission_holds ObjectRef schema resolvers variables fuel fieldType
    fields source path usages context route supply literal
  have unique := (EagerScopes.completeValue_origins schema resolvers variables fuel fieldType fields
    source path usages context false route supply).left.unique
  exact ⟨coverage, omitted, coverage.1.omitted_count unique⟩

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.OriginAccounting
