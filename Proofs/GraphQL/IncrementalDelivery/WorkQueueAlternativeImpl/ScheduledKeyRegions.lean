import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.ScheduledExecutor
import Proofs.GraphQL.IncrementalDelivery.Semantics.ExecutedRefRegions

/-! Fresh-key bounds and stream-region separation for actual recursive cut execution.
Existing RefRegions certificates and constructor lemmas are reused. The checked root
edge derives inherited-context bounds from original collection; callers do not assume
freshness of the scheduled output. Cuts stop allocation but never roll back the supply.

This is a generated single-execution invariant, not construction of a map to eager
execution or native identities. Defers may share inherited keys within a region;
stream-item child regions remain separate. No rank/index data structure is introduced. -/

namespace
  GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.ScheduledExecution

open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Semantics
open GraphQL.IncrementalDelivery.Semantics.RefRegions

variable {ObjectRef : Type}

attribute [local simp] id_pure_eq id_bind_eq id_map_eq run_bind run_map

/-- Every key in the actual scheduled root work lies in its own allocation interval,
and different stream-item regions do not share keys. -/
def RecursiveScheduledKeyRegions : Prop :=
  ∀ (ObjectRef : Type) (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues) fuel parentType (source : ResolverValue ObjectRef)
    selections state,
    Completed [] state
      ((executeRootSelectionSetCore schema resolvers variables fuel parentType source
          selections).run
        state)

/-- Recursive plan leaf, with the explicit inherited-context bound that collection
establishes at real object/root boundaries. -/
def PlanKeyRegions : Prop :=
  ∀ (ObjectRef : Type) (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues) fuel parentType (source : ResolverValue ObjectRef)
    (collection : FieldCollection) path usages context state,
    (∀ key ∈
      (getNewDeferMap collection.newDeferUsages path context).flatMap
        RefRoles.fragmentRefs,
      key < state)
    → Completed
        ((getNewDeferMap collection.newDeferUsages path context).flatMap
          RefRoles.fragmentRefs)
        state
        ((executeExecutionPlan schema resolvers variables fuel parentType source
            collection.newDeferUsages
            (buildExecutionPlan collection.collectedFieldsMap usages) path usages
            context).run
          state)

/-- Checked root reduction: the original collector supplies all plan prerequisites. -/
theorem recursiveScheduledKeyRegions_of_plan (plans : PlanKeyRegions)
    : RecursiveScheduledKeyRegions := by
  intro ObjectRef schema resolvers variables fuel parentType source selections state
  have collectedBounds := OwnerPaths.collectFields_supply schema variables parentType source
    selections none state
  let collected := (collectFields schema variables parentType source selections none).run state
  have planned := plans ObjectRef schema resolvers variables fuel parentType source collected.1
    [] [] [] collected.2 (mapRefs_new_bound [] _ [] _ (by simp)
      (fun usage member => (collectedBounds.2 usage member).2))
  exact planned.rebase collectedBounds.1
    (mapRefs_new_root [] _ [] state
      (fun usage member => (collectedBounds.2 usage member).1))

mutual
  theorem executePlan_regions (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variables : VariableValues) (fuel : Nat) (parentType : Name)
      (source : ResolverValue ObjectRef) (collection : FieldCollection)
      (path : ResponsePath) (usages : List Nat) (deferMap : DeferMap) (state : Nat)
      (hm
        : ∀ key ∈
            (getNewDeferMap collection.newDeferUsages path deferMap).flatMap
              RefRoles.fragmentRefs,
            key < state)
      : Completed
          ((getNewDeferMap collection.newDeferUsages path deferMap).flatMap
            RefRoles.fragmentRefs)
          state
          ((executeExecutionPlan schema resolvers variables fuel parentType source
              collection.newDeferUsages
              (buildExecutionPlan collection.collectedFieldsMap usages) path usages
              deferMap).run
            state) := by
    have hl := executeCollectedFields_regions schema resolvers variables fuel parentType source
      (buildExecutionPlan collection.collectedFieldsMap usages).collectedFieldsMap path usages
      (getNewDeferMap collection.newDeferUsages path deferMap) state hm
    simp only [executeExecutionPlan, run_bind]
    split
    · exact hl
    · have hr := collectExecutionGroups_regions schema resolvers variables fuel parentType source
        (buildExecutionPlan collection.collectedFieldsMap usages).newCollectedFieldsMaps path
        (getNewDeferMap collection.newDeferUsages path deferMap) _
        (fun key hk => Nat.lt_of_lt_of_le (hm key hk) hl.monotone)
      simp only [run_bind, StateT.run_pure, id_pure_eq]
      exact hl.append hr hm
  termination_by (fuel, 6, 0, 0)
  decreasing_by
    all_goals simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right

  theorem collectExecutionGroups_regions (schema : Schema)
      (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
      (parentType : Name) (source : ResolverValue ObjectRef)
      (partitions : List (List Nat × CollectedFieldsMap)) (path : ResponsePath)
      (deferMap : DeferMap) (state : Nat)
      (hm : ∀ key ∈ deferMap.flatMap RefRoles.fragmentRefs, key < state)
      : let output :=
          (collectExecutionGroups schema resolvers variables fuel parentType
            source partitions path deferMap).run
            state
        Output (deferMap.flatMap RefRoles.fragmentRefs) state output.2 output.1 := by
    cases partitions with
    | nil =>
        simpa only [collectExecutionGroups, StateT.run_pure, id_pure_eq] using Output.empty
          (inherited := deferMap.flatMap RefRoles.fragmentRefs) (Nat.le_refl state)
    | cons partition rest =>
        rcases partition with ⟨usages, groups⟩
        have hl := executeCollectedFields_regions schema resolvers variables fuel parentType
          source groups path usages deferMap state hm
        have hr := collectExecutionGroups_regions schema resolvers variables fuel parentType
          source rest path deferMap _ (fun key hk => Nat.lt_of_lt_of_le (hm key hk) hl.monotone)
        have hd := hl.executionGroup (usages.filterMap (lookupDeferredFragment? deferMap)) path
          ((executeCollectedFields schema resolvers variables fuel parentType source groups path
            usages deferMap).run state).1.result (mapRefs_filterMap_subset deferMap usages) hm
        simp only [collectExecutionGroups, run_bind, StateT.run_pure, id_pure_eq]
        exact hd.append hr hm
  termination_by (fuel, 5, 0, sizeOf partitions)
  decreasing_by
    all_goals subst_vars; simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right
    all_goals omega

  theorem executeCollectedFields_regions (schema : Schema)
      (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
      (parentType : Name) (source : ResolverValue ObjectRef) (groups : CollectedFieldsMap)
      (path : ResponsePath) (usages : List Nat) (deferMap : DeferMap) (state : Nat)
      (hm : ∀ key ∈ deferMap.flatMap RefRoles.fragmentRefs, key < state)
      : Completed (deferMap.flatMap RefRoles.fragmentRefs) state
          ((executeCollectedFields schema resolvers variables fuel parentType source
              groups path usages deferMap).run
            state) := by
    cases groups with
    | nil =>
        simpa only [executeCollectedFields, StateT.run_pure, id_pure_eq, Completed,
          Completion.pure]
          using Output.empty (inherited := deferMap.flatMap RefRoles.fragmentRefs)
            (Nat.le_refl state)
    | cons group rest =>
        rcases group with ⟨name, fields⟩
        have hl := executeResponseField_regions schema resolvers variables fuel parentType
          source name
          fields path usages deferMap state hm
        simp only [executeCollectedFields, run_bind]
        split
        · simpa only [StateT.run_pure, id_pure_eq, Completed] using hl
        · have hr := executeCollectedFields_regions schema resolvers variables fuel parentType
            source rest path usages deferMap _
            (fun key hk => Nat.lt_of_lt_of_le (hm key hk) hl.monotone)
          simp only [run_bind, StateT.run_pure, id_pure_eq]
          exact output_combine List.append _ _ hl hr hm
  termination_by (fuel, 4, 0, sizeOf groups)
  decreasing_by
    all_goals subst_vars; simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right
    all_goals omega

  theorem executeResponseField_regions (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variables : VariableValues) (fuel : Nat) (parentType : Name)
      (source : ResolverValue ObjectRef) (name : Name) (fields : List FieldDetails)
      (path : ResponsePath) (usages : List Nat) (deferMap : DeferMap) (state : Nat)
      (hm : ∀ key ∈ deferMap.flatMap RefRoles.fragmentRefs, key < state)
      : Completed (deferMap.flatMap RefRoles.fragmentRefs) state
          ((executeResponseField schema resolvers variables fuel parentType source name
              fields path usages deferMap).run
            state) := by
    cases fuel with
    | zero =>
        simpa only [executeResponseField, StateT.run_pure, id_pure_eq, Completed,
          Completion.error]
          using Output.empty (inherited := deferMap.flatMap RefRoles.fragmentRefs)
            (Nat.le_refl state)
    | succ fuel =>
        cases fields with
        | nil =>
            simpa only [executeResponseField, StateT.run_pure, id_pure_eq, Completed,
              Completion.error]
              using Output.empty (inherited := deferMap.flatMap RefRoles.fragmentRefs)
                (Nat.le_refl state)
        | cons field rest =>
            simp only [executeResponseField]
            split
            · exact Output.empty _ (Nat.le_refl state)
            · split
              · exact Output.empty _ (Nat.le_refl state)
              · split
                · exact Output.empty _ (Nat.le_refl state)
                · simp only [run_bind, StateT.run_pure, id_pure_eq]
                  apply output_map
                  exact completeValue_regions schema resolvers variables fuel _ _ _
                    (path ++ [.field name]) usages deferMap true state hm
  termination_by (fuel, 3, 0, sizeOf fields)
  decreasing_by
    all_goals subst_vars; simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right

  theorem completeValue_regions (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variables : VariableValues) (fuel : Nat) (fieldType : TypeRef)
      (fields : List FieldDetails) (value : ResolverValue ObjectRef)
      (path : ResponsePath) (usages : List Nat) (deferMap : DeferMap) (allowStream : Bool)
      (state : Nat) (hm : ∀ key ∈ deferMap.flatMap RefRoles.fragmentRefs, key < state)
      : Completed (deferMap.flatMap RefRoles.fragmentRefs) state
          ((completeValue schema resolvers variables fuel fieldType fields value path
              usages deferMap allowStream).run
            state) := by
    cases fuel with
    | zero =>
        simpa only [completeValue, StateT.run_pure, id_pure_eq, Completed,
          Completion.error]
          using Output.empty (inherited := deferMap.flatMap RefRoles.fragmentRefs)
            (Nat.le_refl state)
    | succ fuel =>
        cases fieldType with
        | nonNull inner =>
            have h := completeValue_regions schema resolvers variables (fuel + 1) inner fields value
              path usages deferMap allowStream state hm
            simp only [completeValue, run_bind, StateT.run_pure, id_pure_eq]
            exact output_nonNull _ h
        | named parentType =>
            cases value with
            | null =>
                simpa only [completeValue, StateT.run_pure, id_pure_eq, Completed,
                  Completion.pure]
                  using Output.empty (inherited := deferMap.flatMap RefRoles.fragmentRefs)
                    (Nat.le_refl state)
            | scalar scalar =>
                simp only [completeValue]; split <;> exact Output.empty _ (Nat.le_refl state)
            | list items =>
                simpa only [completeValue, StateT.run_pure, id_pure_eq, Completed,
                  Completion.error]
                  using Output.empty (inherited := deferMap.flatMap RefRoles.fragmentRefs)
                    (Nat.le_refl state)
            | object runtimeType ref =>
                simp only [completeValue]
                split
                · exact Output.empty _ (Nat.le_refl state)
                · have hc := OwnerPaths.collectSubfields_supply schema variables runtimeType
                    (.object runtimeType ref) fields state
                  have h := executePlan_regions schema resolvers variables fuel runtimeType
                    (.object runtimeType ref) _ path usages deferMap _
                    (mapRefs_new_bound deferMap _ path _
                      (fun key hk => Nat.lt_of_lt_of_le (hm key hk) hc.1)
                      (fun usage hu => (hc.2 usage hu).2))
                  simp only [run_bind, StateT.run_pure, id_pure_eq]
                  apply output_catchNull
                  exact h.rebase hc.1 (mapRefs_new_root deferMap _ path state
                    (fun usage hu => (hc.2 usage hu).1))
        | list inner =>
            cases value with
            | null =>
                simpa only [completeValue, StateT.run_pure, id_pure_eq, Completed,
                  Completion.pure]
                  using Output.empty (inherited := deferMap.flatMap RefRoles.fragmentRefs)
                    (Nat.le_refl state)
            | scalar scalar =>
                simpa only [completeValue, StateT.run_pure, id_pure_eq, Completed,
                  Completion.error]
                  using Output.empty (inherited := deferMap.flatMap RefRoles.fragmentRefs)
                    (Nat.le_refl state)
            | object runtimeType ref =>
                simpa only [completeValue, StateT.run_pure, id_pure_eq, Completed,
                  Completion.error]
                  using Output.empty (inherited := deferMap.flatMap RefRoles.fragmentRefs)
                    (Nat.le_refl state)
            | list items =>
                simpa only [completeValue] using completeListValueWithStream_regions
                  schema resolvers variables
                  fuel inner fields items path usages deferMap allowStream state hm
  termination_by (fuel, 1, sizeOf fieldType, 0)
  decreasing_by
    all_goals subst_vars; simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right

  theorem completeListValueWithStream_regions (schema : Schema)
      (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
      (inner : TypeRef) (fields : List FieldDetails)
      (values : List (ResolverValue ObjectRef)) (path : ResponsePath) (usages : List Nat)
      (deferMap : DeferMap) (allowStream : Bool) (state : Nat)
      (hm : ∀ key ∈ deferMap.flatMap RefRoles.fragmentRefs, key < state)
      : Completed (deferMap.flatMap RefRoles.fragmentRefs) state
          ((completeListValueWithStream schema resolvers variables fuel inner fields
              values path usages deferMap allowStream).run
            state) := by
    unfold completeListValueWithStream
    dsimp only
    split
    · exact Output.empty _ (Nat.le_refl state)
    · have h := completeListValue_regions schema resolvers variables fuel inner fields values
        path 0 usages deferMap state hm
      simp only [run_bind, StateT.run_pure, id_pure_eq]
      exact output_catchNull _ _ h
    · rename_i usage _
      have hl := completeListValue_regions schema resolvers variables fuel inner fields
        (values.take usage.initialCount) path 0 usages deferMap state hm
      simp only [run_bind]
      split
      · exact output_catchNull _ _ hl
      · split
        · exact output_catchNull _ _ hl
        · let middle := ((completeListValue schema resolvers variables fuel inner fields
            (values.take usage.initialCount) path 0 usages deferMap).run state).2
          have hr := completeStreamItems_regions schema resolvers variables fuel inner
            (fields.map (fun field => {field with deferUsage := none}))
            (values.drop usage.initialCount) path usage.initialCount (middle + 1)
          simp only [freshNodeRef, run_bind, StateT.run_get, StateT.run_set, StateT.run_pure, id_pure_eq]
          apply Output.append (output_catchNull _ _ hl) _ hm
          exact Output.stream _ {ref := middle, path := path, label := usage.label} hr
  termination_by (fuel, 3, 0, 0)
  decreasing_by
    all_goals subst_vars; simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right

  theorem completeListValue_regions (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variables : VariableValues) (fuel : Nat) (itemType : TypeRef)
      (fields : List FieldDetails) (values : List (ResolverValue ObjectRef))
      (path : ResponsePath) (index : Nat) (usages : List Nat) (deferMap : DeferMap)
      (state : Nat) (hm : ∀ key ∈ deferMap.flatMap RefRoles.fragmentRefs, key < state)
      : Completed (deferMap.flatMap RefRoles.fragmentRefs) state
          ((completeListValue schema resolvers variables fuel itemType fields values path
              index usages deferMap).run
            state) := by
    cases values with
    | nil =>
        simpa only [completeListValue, StateT.run_pure, id_pure_eq, Completed,
          Completion.pure]
          using Output.empty (inherited := deferMap.flatMap RefRoles.fragmentRefs)
            (Nat.le_refl state)
    | cons value rest =>
        have hl := completeValue_regions schema resolvers variables fuel itemType fields value
          (path ++ [.index index]) usages deferMap false state hm
        simp only [completeListValue, run_bind]
        split
        · simpa only [StateT.run_pure, id_pure_eq, Completion.error, Completed]
            using Output.empty (deferMap.flatMap RefRoles.fragmentRefs) hl.monotone
        · have hr := completeListValue_regions schema resolvers variables fuel itemType fields rest
            path (index + 1) usages deferMap _
            (fun key hk => Nat.lt_of_lt_of_le (hm key hk) hl.monotone)
          simp only [run_bind, StateT.run_pure, id_pure_eq]
          exact output_combine List.cons _ _ hl hr hm
  termination_by (fuel, 2, sizeOf itemType, sizeOf values)
  decreasing_by
    all_goals subst_vars; simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right
    all_goals omega

  theorem completeStreamItems_regions (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variables : VariableValues) (fuel : Nat) (itemType : TypeRef)
      (fields : List FieldDetails) (values : List (ResolverValue ObjectRef))
      (path : ResponsePath) (index state : Nat)
      : let output :=
          (completeStreamItems schema resolvers variables fuel itemType fields
            values path index).run
            state
        ItemsOutput state output.2 output.1 := by
    cases values with
    | nil =>
        simpa only [completeStreamItems, StateT.run_pure, id_pure_eq] using ItemsOutput.empty
          (Nat.le_refl state)
    | cons value rest =>
        have hl := completeValue_regions schema resolvers variables fuel itemType fields value
          (path ++ [.index index]) [] [] false state (by simp)
        simp only [completeStreamItems, run_bind]
        split
        · simp only [StateT.run_pure, id_pure_eq]
          exact ItemsOutput.cons (Output.empty [] hl.monotone) (ItemsOutput.empty (Nat.le_refl _)) _
        · have hr := completeStreamItems_regions schema resolvers variables fuel itemType fields rest
            path (index + 1)
            ((completeValue schema resolvers variables fuel itemType fields value
              (path ++ [.index index]) [] [] false).run state).2
          simp only [run_bind, StateT.run_pure, id_pure_eq]
          exact ItemsOutput.cons hl hr _
  termination_by (fuel, 2, sizeOf itemType, sizeOf values)
  decreasing_by
    all_goals subst_vars; simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right
    all_goals omega
end

/-- All recursive plan leaves are discharged by the actual execution branches. -/
theorem planKeyRegions_holds : PlanKeyRegions :=
  fun _ schema resolvers variables fuel parentType source collection path usages context
      state bound =>
    executePlan_regions schema resolvers variables fuel parentType source collection
      path usages context state bound

/-- Full generated root certificate, without a freshness or eager-correspondence premise. -/
theorem recursiveScheduledKeyRegions_holds : RecursiveScheduledKeyRegions :=
  recursiveScheduledKeyRegions_of_plan planKeyRegions_holds

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.ScheduledExecution
