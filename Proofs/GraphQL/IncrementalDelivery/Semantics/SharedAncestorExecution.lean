import Proofs.GraphQL.IncrementalDelivery.Semantics.SharedAncestorExecutor
import Proofs.GraphQL.IncrementalDelivery.Semantics.AncestryContext
import Proofs.GraphQL.IncrementalDelivery.Semantics.Planning

/-! Recursive shared-construction refinement, with no new public assumptions.
The graph root is `RootExecutionExact`; `PlanRefinement` supplies its checked reduction.
Recursive leaves carry one extending ghost assignment through siblings and stream resets.
Equality includes the complete work tree, all descriptors/outcomes, and fresh-key supply. -/

namespace GraphQL.IncrementalDelivery.Semantics.SharedAncestorExecution

open GraphQL.IncrementalDelivery.Execution
open Ancestry SharedAncestorConstruction

attribute [local simp] id_pure_eq id_bind_eq id_map_eq run_bind run_map

/-- The same ghost assignment extends through the actual fresh-key supply. -/
def Advances (parents : Assignment) (start finish : Nat) : Prop :=
  start ≤ finish ∧ ∃ next, Extends start parents next ∧ Valid next finish

/-- Exact execution equality together with the evidence needed by the next sibling. -/
def Refines (parents : Assignment) (state : Nat) (optimized original : StateM Nat α)
    : Prop :=
  optimized.run state = original.run state ∧ Advances parents state (original.run state).2

theorem Refines.pure (parents : Assignment) (state : Nat) (value : α)
    (valid : Valid parents state)
    : Refines parents state (pure value) (pure value) :=
  ⟨rfl, Nat.le_refl _, parents, Extends.refl _ _, valid⟩

theorem Refines.bind {parents : Assignment} {state : Nat}
    {left right : StateM Nat α} {nextLeft nextRight : α → StateM Nat β}
    (first : Refines parents state left right)
    (later
      : ∀ next,
          state ≤ (right.run state).2
          → Extends state parents next
          → Valid next (right.run state).2
          → Refines next (right.run state).2
              (nextLeft (right.run state).1) (nextRight (right.run state).1))
    : Refines parents state (left >>= nextLeft) (right >>= nextRight) := by
  obtain ⟨equal, hle, middle, extended, valid⟩ := first
  obtain ⟨tail, hlt, final, extension, finalValid⟩ := later middle hle extended valid
  refine ⟨?_, Nat.le_trans hle hlt, final, extended.trans extension hle, finalValid⟩
  simpa only [run_bind, equal] using tail

theorem Refines.map {parents : Assignment} {state : Nat}
    {left right : StateM Nat α} (first : Refines parents state left right) (f : α → β)
    : Refines parents state
        (do
          return f (← left))
        (do
          return f (← right)) :=
  first.bind (fun next _ _ valid => Refines.pure next _ _ valid)

/-- Collection may choose its particular extended assignment for the recursive tail. -/
theorem Refines.bind_of {parents next : Assignment} {state : Nat}
    {left right : StateM Nat α} {nextLeft nextRight : α → StateM Nat β}
    (equal : left.run state = right.run state) (hle : state ≤ (right.run state).2)
    (extended : Extends state parents next)
    (later
      : Refines next (right.run state).2
          (nextLeft (right.run state).1) (nextRight (right.run state).1))
    : Refines parents state (left >>= nextLeft) (right >>= nextRight) := by
  obtain ⟨tail, hlt, final, extension, valid⟩ := later
  refine ⟨?_, Nat.le_trans hle hlt, final, extended.trans extension hle, valid⟩
  simpa only [run_bind, equal] using tail

theorem Refines.fresh (parents : Assignment) (state : Nat) (valid : Valid parents state)
    : Refines parents state freshNodeRef freshNodeRef := by
  refine ⟨rfl, Nat.le_succ _, allocate parents state [], allocate_extends _ _ _, ?_⟩
  exact allocate_valid parents state none valid (by simp)

/-- Generated plan boundary, including every inherited-context construction obligation. -/
def PlanRefinement : Prop :=
  ∀ (ObjectRef : Type) (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues) fuel parentType (source : ResolverValue ObjectRef)
    (collection : FieldCollection) path usages context parents state,
    Valid parents state
    → MapAt parents state (getNewDeferMap collection.newDeferUsages path context)
    → GroupsSatisfy
        (fun field =>
          OptionalUsageAt parents state
            (getNewDeferMap collection.newDeferUsages path context) field.deferUsage)
        collection.collectedFieldsMap
    → Coherent context
    → ReuseTrace path collection.newDeferUsages context
    → Refines parents state
        (executeExecutionPlan schema resolvers variables fuel parentType source
          collection.newDeferUsages
          (buildExecutionPlan collection.collectedFieldsMap usages) path usages context)
        (Execution.executeExecutionPlan schema resolvers variables fuel parentType source
          collection.newDeferUsages
          (buildExecutionPlan collection.collectedFieldsMap usages) path usages context)

/-- Root target: arbitrary finite pure execution, with no context or host premise. -/
def RootExecutionExact : Prop :=
  ∀ (ObjectRef : Type) (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues) fuel parentType (source : ResolverValue ObjectRef)
    selections state,
    (executeRootSelectionSetCore schema resolvers variables fuel parentType source
      selections).run
      state
    = (Execution.executeRootSelectionSetCore schema resolvers variables fuel parentType
        source selections).run
        state

/-- Checked root edge: collection derives every prerequisite of recursive refinement. -/
theorem rootExecutionExact_of_planRefinement (plan : PlanRefinement)
    : RootExecutionExact := by
  intro ObjectRef schema resolvers variables fuel parentType source selections state
  obtain ⟨_, middle, _, valid, metadata, known⟩ := collectFields_ancestry schema variables
    parentType source selections none (fun _ => []) state [] []
    (by simp [Valid]) (by simp [MapAt]) (by simp [OptionalUsageAt])
  have exactPlan := plan ObjectRef schema resolvers variables fuel parentType source _
    [] [] [] middle _ valid metadata known coherent_empty
    (collectFields_reuseTrace schema variables parentType source selections none
      (fun _ => []) state [] [] (by simp [Valid]) (by simp [MapAt])
      (by simp [OptionalUsageAt]))
  simpa only [executeRootSelectionSetCore, Execution.executeRootSelectionSetCore,
    run_bind]
    using exactPlan.1

mutual
  theorem executePlan_refines (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variables : VariableValues) (fuel : Nat) (parentType : Name)
      (source : ResolverValue ObjectRef) (collection : FieldCollection)
      (path : ResponsePath) (usages : List Nat) (context : DeferMap)
      (parents : Assignment) (state : Nat) (valid : Valid parents state)
      (metadata
        : MapAt parents state (getNewDeferMap collection.newDeferUsages path context))
      (known
        : GroupsSatisfy
            (fun field =>
              OptionalUsageAt parents state
                (getNewDeferMap collection.newDeferUsages path context) field.deferUsage)
            collection.collectedFieldsMap)
      (coherent : Coherent context)
      (trace : ReuseTrace path collection.newDeferUsages context)
      : Refines parents state
          (executeExecutionPlan schema resolvers variables fuel parentType source
            collection.newDeferUsages
            (buildExecutionPlan collection.collectedFieldsMap usages) path usages context)
          (Execution.executeExecutionPlan schema resolvers variables fuel parentType
            source collection.newDeferUsages
            (buildExecutionPlan collection.collectedFieldsMap usages) path usages
            context) := by
    have partitioned := buildExecutionPlan_preserves_property _
      collection.collectedFieldsMap usages known
    have newCoherent := coherent_getNewDeferMap collection.newDeferUsages path coherent
    simp only [executeExecutionPlan, Execution.executeExecutionPlan, build_eq coherent trace]
    apply (executeCollectedFields_refines schema resolvers variables fuel parentType
            source _ path usages _ parents state valid metadata partitioned.1
            newCoherent).bind
    intro middle hle he hv
    cases result
          : ((Execution.executeCollectedFields schema resolvers variables fuel parentType
                source
                (buildExecutionPlan collection.collectedFieldsMap
                  usages).collectedFieldsMap
                path usages (getNewDeferMap collection.newDeferUsages path context)).run
              state).1.result with
    | error errors =>
        exact Refines.pure middle _ _ hv
    | ok data =>
        apply (collectExecutionGroups_refines schema resolvers variables fuel parentType
          source _ path _ middle _ hv (metadata.extend he hle)
          (fun p hp => groupsKnown_extend (partitioned.2 p hp) he hle) newCoherent).map
  termination_by (fuel, 6, 0, 0)
  decreasing_by
    all_goals simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right

  theorem collectExecutionGroups_refines (schema : Schema)
      (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
      (parentType : Name) (source : ResolverValue ObjectRef)
      (partitions : List (List Nat × CollectedFieldsMap)) (path : ResponsePath)
      (context : DeferMap) (parents : Assignment) (state : Nat)
      (valid : Valid parents state) (metadata : MapAt parents state context)
      (known
        : ∀ partition ∈ partitions,
            GroupsSatisfy
              (fun field => OptionalUsageAt parents state context field.deferUsage)
              partition.2)
      (coherent : Coherent context)
      : Refines parents state
          (collectExecutionGroups schema resolvers variables fuel parentType source
            partitions path context)
          (Execution.collectExecutionGroups schema resolvers variables fuel parentType
            source partitions path context) := by
    cases partitions with
    | nil =>
        simpa only [collectExecutionGroups, Execution.collectExecutionGroups]
          using Refines.pure parents state Work.empty valid
    | cons partition rest =>
        rcases partition with ⟨usages, groups⟩
        simp only [collectExecutionGroups, Execution.collectExecutionGroups,
          Execution.executeExecutionGroup]
        apply (executeCollectedFields_refines schema resolvers variables fuel parentType
                source groups path usages context parents state valid metadata
                (known (usages, groups) (by simp)) coherent).bind
        intro middle hle he hv
        apply (collectExecutionGroups_refines schema resolvers variables fuel parentType
                source rest path context middle _ hv (metadata.extend he hle)
                (fun p hp =>
                  groupsKnown_extend (known p (List.mem_cons_of_mem _ hp)) he hle)
                coherent).map
  termination_by (fuel, 5, 0, sizeOf partitions)
  decreasing_by
    all_goals subst_vars; simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right
    all_goals try omega

  theorem executeCollectedFields_refines (schema : Schema)
      (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
      (parentType : Name) (source : ResolverValue ObjectRef) (groups : CollectedFieldsMap)
      (path : ResponsePath) (usages : List Nat) (context : DeferMap)
      (parents : Assignment) (state : Nat) (valid : Valid parents state)
      (metadata : MapAt parents state context)
      (known
        : GroupsSatisfy
            (fun field => OptionalUsageAt parents state context field.deferUsage) groups)
      (coherent : Coherent context)
      : Refines parents state
          (executeCollectedFields schema resolvers variables fuel parentType source groups
            path usages context)
          (Execution.executeCollectedFields schema resolvers variables fuel parentType
            source groups path usages context) := by
    cases groups with
    | nil =>
        simpa only [executeCollectedFields, Execution.executeCollectedFields]
          using Refines.pure parents state (Completion.pure []) valid
    | cons group rest =>
        rcases group with ⟨name, fields⟩
        simp only [executeCollectedFields, Semantics.executeCollectedFields_cons]
        apply (executeResponseField_refines schema resolvers variables fuel parentType
                source name fields path usages context parents state valid metadata
                (known (name, fields) (by simp)) coherent).bind
        intro middle hle he hv
        apply (executeCollectedFields_refines schema resolvers variables fuel parentType
                source rest path usages context middle _ hv (metadata.extend he hle)
                (groupsKnown_extend (fun g hg => known g (List.mem_cons_of_mem _ hg)) he
                  hle)
                coherent).map
  termination_by (fuel, 4, 0, sizeOf groups)
  decreasing_by
    all_goals subst_vars; simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right
    all_goals try omega

  theorem executeResponseField_refines (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variables : VariableValues) (fuel : Nat) (parentType : Name)
      (source : ResolverValue ObjectRef) (name : Name) (fields : List FieldDetails)
      (path : ResponsePath) (usages : List Nat) (context : DeferMap)
      (parents : Assignment) (state : Nat) (valid : Valid parents state)
      (metadata : MapAt parents state context)
      (known : ∀ field ∈ fields, OptionalUsageAt parents state context field.deferUsage)
      (coherent : Coherent context)
      : Refines parents state
          (executeResponseField schema resolvers variables fuel parentType source name
            fields path usages context)
          (Semantics.executeResponseField schema resolvers variables fuel parentType
            source name fields path usages context) := by
    cases fuel with
    | zero =>
        simpa only [executeResponseField, Semantics.executeResponseField]
          using Refines.pure parents state (Completion.error 1) valid
    | succ fuel =>
        cases fields with
        | nil =>
            simpa only [executeResponseField, Semantics.executeResponseField]
              using Refines.pure parents state (Completion.error 1) valid
        | cons field rest =>
            simp only [executeResponseField, Semantics.executeResponseField]
            split
            · simp_all only
              exact Refines.pure parents state _ valid
            · split
              · simp_all only
                exact Refines.pure parents state _ valid
              · split
                · simp_all only
                  exact Refines.pure parents state _ valid
                · simp_all only
                  exact (completeValue_refines schema resolvers variables fuel _ _ _
                    (path ++ [.field name]) usages context true parents state valid metadata
                    known coherent).map _
  termination_by (fuel, 3, 0, sizeOf fields)
  decreasing_by
    all_goals subst_vars; simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right

  theorem completeValue_refines (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variables : VariableValues) (fuel : Nat) (fieldType : TypeRef)
      (fields : List FieldDetails) (value : ResolverValue ObjectRef)
      (path : ResponsePath) (usages : List Nat) (context : DeferMap) (allowStream : Bool)
      (parents : Assignment) (state : Nat) (valid : Valid parents state)
      (metadata : MapAt parents state context)
      (known : ∀ field ∈ fields, OptionalUsageAt parents state context field.deferUsage)
      (coherent : Coherent context)
      : Refines parents state
          (completeValue schema resolvers variables fuel fieldType fields value path
            usages context allowStream)
          (Execution.completeValue schema resolvers variables fuel fieldType fields value
            path usages context allowStream) := by
    cases fuel with
    | zero =>
        simpa only [completeValue, Execution.completeValue]
          using Refines.pure parents state (Completion.error 1) valid
    | succ fuel =>
        cases fieldType with
        | nonNull inner =>
            simpa only [completeValue, Execution.completeValue]
              using (completeValue_refines schema resolvers variables (fuel + 1) inner
                      fields value path usages context allowStream parents state valid
                      metadata known coherent).map
                Completion.nonNull
        | named parentType =>
            cases value with
            | null =>
                simpa only [completeValue, Execution.completeValue]
                  using Refines.pure parents state (Completion.pure ResponseValue.null)
                    valid
            | scalar scalar =>
                simp only [completeValue, Execution.completeValue]
                split <;> exact Refines.pure parents state _ valid
            | list items =>
                simpa only [completeValue, Execution.completeValue]
                  using Refines.pure parents state (Completion.error 1) valid
            | object runtimeType ref =>
                simp only [completeValue, Execution.completeValue]
                split
                · exact Refines.pure parents state _ valid
                · obtain ⟨hsc, middle, he, hv, hm, hk⟩ := collectSubfields_ancestry schema
                    variables runtimeType (.object runtimeType ref) fields parents state context
                    path valid metadata known
                  have trace := collectSubfields_reuseTrace schema variables runtimeType
                    (.object runtimeType ref) fields parents state context path valid metadata known
                  apply Refines.bind_of rfl hsc he
                  exact (executePlan_refines schema resolvers variables fuel runtimeType
                    (.object runtimeType ref) _ path usages context middle _ hv hm hk
                    coherent trace).map (Completion.catchNull ResponseValue.object)
        | list inner =>
            cases value with
            | null =>
                simpa only [completeValue, Execution.completeValue]
                  using Refines.pure parents state (Completion.pure ResponseValue.null)
                    valid
            | scalar scalar =>
                simpa only [completeValue, Execution.completeValue]
                  using Refines.pure parents state (Completion.error 1) valid
            | object runtimeType ref =>
                simpa only [completeValue, Execution.completeValue]
                  using Refines.pure parents state (Completion.error 1) valid
            | list items =>
                simpa only [completeValue, Execution.completeValue]
                  using completeListValueWithStream_refines schema resolvers variables
                    fuel inner fields items path usages context allowStream parents state
                    valid metadata known coherent
  termination_by (fuel, 1, sizeOf fieldType, 0)
  decreasing_by
    all_goals subst_vars; simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right

  theorem completeListValueWithStream_refines (schema : Schema)
      (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
      (inner : TypeRef) (fields : List FieldDetails)
      (values : List (ResolverValue ObjectRef)) (path : ResponsePath) (usages : List Nat)
      (context : DeferMap) (allowStream : Bool) (parents : Assignment) (state : Nat)
      (valid : Valid parents state) (metadata : MapAt parents state context)
      (known : ∀ field ∈ fields, OptionalUsageAt parents state context field.deferUsage)
      (coherent : Coherent context)
      : Refines parents state
          (completeListValueWithStream schema resolvers variables fuel inner fields values
            path usages context allowStream)
          (Execution.completeListValueWithStream schema resolvers variables fuel inner
            fields values path usages context allowStream) := by
    simp only [completeListValueWithStream, Execution.completeListValueWithStream]
    split
    · simp_all only
      exact Refines.pure parents state _ valid
    · simp_all only
      exact (completeListValue_refines schema resolvers variables fuel inner fields values
        path 0 usages context parents state valid metadata known coherent).map
        (Completion.catchNull ResponseValue.list)
    · rename_i usage _
      simp_all only
      apply (completeListValue_refines schema resolvers variables fuel inner fields
              (values.take usage.initialCount) path 0 usages context parents state valid
              metadata known coherent).bind
      intro middle hle he hv
      cases result
            : ((Execution.completeListValue schema resolvers variables fuel inner fields
                  (values.take usage.initialCount) path 0 usages context).run
                state).1.result with
      | error errors =>
          exact Refines.pure middle _ _ hv
      | ok data =>
          simp only
          split
          · exact Refines.pure middle _ _ hv
          · apply (Refines.fresh middle _ hv).bind
            intro next _ _ nextValid
            apply (completeStreamItems_refines schema resolvers variables fuel inner
              (fields.map (fun field => { field with deferUsage := none }))
              (values.drop usage.initialCount) path usage.initialCount next _ nextValid
              (by intro f hf; obtain ⟨old, _, rfl⟩ := List.mem_map.mp hf; rfl)).map
  termination_by (fuel, 3, 0, 0)
  decreasing_by
    all_goals subst_vars; simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right

  theorem completeListValue_refines (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variables : VariableValues) (fuel : Nat) (itemType : TypeRef)
      (fields : List FieldDetails) (values : List (ResolverValue ObjectRef))
      (path : ResponsePath) (index : Nat) (usages : List Nat) (context : DeferMap)
      (parents : Assignment) (state : Nat) (valid : Valid parents state)
      (metadata : MapAt parents state context)
      (known : ∀ field ∈ fields, OptionalUsageAt parents state context field.deferUsage)
      (coherent : Coherent context)
      : Refines parents state
          (completeListValue schema resolvers variables fuel itemType fields values path
            index usages context)
          (Execution.completeListValue schema resolvers variables fuel itemType fields
            values path index usages context) := by
    cases values with
    | nil =>
        simpa only [completeListValue, Execution.completeListValue]
          using Refines.pure parents state (Completion.pure []) valid
    | cons value rest =>
        simp only [completeListValue, Execution.completeListValue]
        apply (completeValue_refines schema resolvers variables fuel itemType fields value
          (path ++ [ResponsePathSegment.index index]) usages context false parents state
          valid metadata known
          coherent).bind
        intro middle hle he hv
        apply (completeListValue_refines schema resolvers variables fuel itemType fields rest path
          (index + 1) usages context middle _ hv (metadata.extend he hle)
          (fieldsKnown_extend known he hle) coherent).map
  termination_by (fuel, 2, sizeOf itemType, sizeOf values)
  decreasing_by
    all_goals subst_vars; simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right
    all_goals try omega

  theorem completeStreamItems_refines (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variables : VariableValues) (fuel : Nat) (itemType : TypeRef)
      (fields : List FieldDetails) (values : List (ResolverValue ObjectRef))
      (path : ResponsePath) (index : Nat) (parents : Assignment) (state : Nat)
      (valid : Valid parents state) (cleared : ∀ field ∈ fields, field.deferUsage = none)
      : Refines parents state
          (completeStreamItems schema resolvers variables fuel itemType fields values path
            index)
          (Execution.completeStreamItems schema resolvers variables fuel itemType fields
            values path index) := by
    cases values with
    | nil =>
        simpa only [completeStreamItems, Execution.completeStreamItems]
          using Refines.pure parents state [] valid
    | cons value rest =>
        simp only [completeStreamItems, Execution.completeStreamItems]
        apply (completeValue_refines schema resolvers variables fuel itemType fields value
                (path ++ [ResponsePathSegment.index index])
                [] [] false parents state valid
                (by simp [MapAt])
                (by intro f hf; simp [OptionalUsageAt, cleared f hf])
                coherent_empty).bind
        intro middle _ _ hv
        cases result
              : ((Execution.completeValue schema resolvers variables fuel itemType fields
                    value (path ++ [.index index]) [] [] false).run
                  state).1.result with
        | error errors =>
            exact Refines.pure middle _ _ hv
        | ok data =>
            apply (completeStreamItems_refines schema resolvers variables fuel itemType fields
              rest path (index + 1) middle _ hv cleared).map
  termination_by (fuel, 2, sizeOf itemType, sizeOf values)
  decreasing_by
    all_goals subst_vars; simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right
    all_goals try omega
end

theorem planRefinement_holds : PlanRefinement := by
  intro ObjectRef schema resolvers variables fuel parentType source collection path usages
    context parents state valid metadata known coherent trace
  exact executePlan_refines schema resolvers variables fuel parentType source collection
    path usages context parents state valid metadata known coherent trace

theorem rootExecutionExact_holds : RootExecutionExact :=
  rootExecutionExact_of_planRefinement planRefinement_holds

/-- Equality of the full state action permits substitution under any unchanged wrapper. -/
theorem executeRootSelectionSetCore_eq (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues) (fuel : Nat) (parentType : Name)
    (source : ResolverValue ObjectRef) (selections : List Selection)
    : executeRootSelectionSetCore schema resolvers variables fuel parentType source
        selections
      = Execution.executeRootSelectionSetCore schema resolvers variables fuel parentType
          source selections := by
  funext state
  exact rootExecutionExact_holds ObjectRef schema resolvers variables fuel parentType source
    selections state

end GraphQL.IncrementalDelivery.Semantics.SharedAncestorExecution
