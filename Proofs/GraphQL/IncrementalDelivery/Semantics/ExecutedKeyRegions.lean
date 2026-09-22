import Proofs.GraphQL.IncrementalDelivery.Semantics.KeyRegions
import Proofs.GraphQL.IncrementalDelivery.Semantics.CollectedKeyRegions

/-! Actual mixed execution separates every stream item's key region. Inherited
defer metadata may be shared within the current region, but hidden item regions
allocate entirely fresh keys. Errors may discard work without changing this fact.
-/

namespace GraphQL.IncrementalDelivery.Semantics.KeyRegions

open GraphQL.IncrementalDelivery.Execution

attribute [local simp] id_pure_eq id_bind_eq id_map_eq run_bind run_map

def Completed (inherited : List Nat) (start : Nat) (output : Completion α × Nat) : Prop :=
  Output inherited start output.2 output.1.work

theorem output_combine {inherited : List Nat} {start middle finish : Nat}
    (f : α → β → γ) (left : Completion α) (right : Completion β)
    (hl : Output inherited start middle left.work)
    (hr : Output inherited middle finish right.work)
    (hi : ∀ key ∈ inherited, key < start)
    : Output inherited start finish (Completion.combine f left right).work := by
  cases hleft : left.result <;> cases hright : right.result <;>
    simp only [Completion.combine, hleft, hright, GraphQL.Execution.Result.combine, Completion.error]
  all_goals first | exact hl.append hr hi | exact Output.empty _ (Nat.le_trans hl.monotone hr.monotone)

theorem output_map {inherited : List Nat} {start finish : Nat} (f : α → β)
    (completed : Completion α) (h : Output inherited start finish completed.work)
    : Output inherited start finish (completed.map f).work := by
  cases he : completed.result <;> simp only [Completion.map, he]
  · exact Output.empty _ h.monotone
  · exact h

theorem output_catchNull {inherited : List Nat} {start finish : Nat}
    (f : α → ResponseValue) (completed : Completion α)
    (h : Output inherited start finish completed.work)
    : Output inherited start finish (completed.catchNull f).work := by
  cases he : completed.result <;> simp only [Completion.catchNull, he]
  · exact Output.empty _ h.monotone
  · exact h

theorem output_nonNull {inherited : List Nat} {start finish : Nat}
    (completed : Completion ResponseValue)
    (h : Output inherited start finish completed.work)
    : Output inherited start finish completed.nonNull.work := by
  unfold Completion.nonNull
  split
  · exact Output.empty _ h.monotone
  · exact h

mutual
  theorem executePlan_regions (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variables : VariableValues) (fuel : Nat) (parentType : Name)
      (source : ResolverValue ObjectRef) (collection : FieldCollection)
      (path : ResponsePath) (usages : List Nat) (deferMap : DeferMap) (state : Nat)
      (hm
        : ∀ key ∈
            (getNewDeferMap collection.newDeferUsages path deferMap).flatMap
              KeyRoles.fragmentKeys,
            key < state)
      : Completed
          ((getNewDeferMap collection.newDeferUsages path deferMap).flatMap
            KeyRoles.fragmentKeys)
          state
          ((executeExecutionPlan schema resolvers variables fuel parentType source
              collection.newDeferUsages (buildExecutionPlan collection.fields usages) path
              usages deferMap).run
            state) := by
    have hl := executeCollectedFields_regions schema resolvers variables fuel parentType source
      (buildExecutionPlan collection.fields usages).collectedFieldsMap path usages
      (getNewDeferMap collection.newDeferUsages path deferMap) state hm
    simp only [executeExecutionPlan, run_bind]
    split
    · exact hl
    · have hr := collectExecutionGroups_regions schema resolvers variables fuel parentType source
        (buildExecutionPlan collection.fields usages).newCollectedFieldsMaps path
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
      (hm : ∀ key ∈ deferMap.flatMap KeyRoles.fragmentKeys, key < state)
      : let output :=
          (collectExecutionGroups schema resolvers variables fuel parentType
            source partitions path deferMap).run
            state
        Output (deferMap.flatMap KeyRoles.fragmentKeys) state output.2 output.1 := by
    cases partitions with
    | nil =>
        simpa only [collectExecutionGroups, StateT.run_pure, id_pure_eq] using Output.empty
          (inherited := deferMap.flatMap KeyRoles.fragmentKeys) (Nat.le_refl state)
    | cons partition rest =>
        rcases partition with ⟨usages, groups⟩
        have hl := executeCollectedFields_regions schema resolvers variables fuel parentType
          source groups path usages deferMap state hm
        have hr := collectExecutionGroups_regions schema resolvers variables fuel parentType
          source rest path deferMap _ (fun key hk => Nat.lt_of_lt_of_le (hm key hk) hl.monotone)
        have hd := hl.executionGroup (usages.filterMap (lookupDeferredFragment? deferMap)) path
          ((executeCollectedFields schema resolvers variables fuel parentType source groups path
            usages deferMap).run state).1.result (mapKeys_filterMap_subset deferMap usages) hm
        simp only [collectExecutionGroups, executeExecutionGroup, run_bind, StateT.run_pure, id_pure_eq]
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
      (hm : ∀ key ∈ deferMap.flatMap KeyRoles.fragmentKeys, key < state)
      : Completed (deferMap.flatMap KeyRoles.fragmentKeys) state
          ((executeCollectedFields schema resolvers variables fuel parentType source
              groups path usages deferMap).run
            state) := by
    cases groups with
    | nil =>
        simpa only [executeCollectedFields_nil, StateT.run_pure, id_pure_eq, Completed,
          Completion.pure]
          using Output.empty (inherited := deferMap.flatMap KeyRoles.fragmentKeys)
            (Nat.le_refl state)
    | cons group rest =>
        rcases group with ⟨name, fields⟩
        have hl := executeResponseField_regions schema resolvers variables fuel parentType
          source name
          fields path usages deferMap state hm
        have hr := executeCollectedFields_regions schema resolvers variables fuel parentType
          source rest path usages deferMap _ (fun key hk => Nat.lt_of_lt_of_le (hm key hk) hl.monotone)
        simp only [executeCollectedFields_cons, run_bind, StateT.run_pure, id_pure_eq]
        exact output_combine List.append _ _ hl hr hm
  termination_by (fuel, 4, 0, sizeOf groups)
  decreasing_by
    all_goals subst_vars; simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right
    all_goals omega

  theorem executeResponseField_regions (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variables : VariableValues) (fuel : Nat) (parentType : Name)
      (source : ResolverValue ObjectRef) (name : Name) (fields : List ExecutableField)
      (path : ResponsePath) (usages : List Nat) (deferMap : DeferMap) (state : Nat)
      (hm : ∀ key ∈ deferMap.flatMap KeyRoles.fragmentKeys, key < state)
      : Completed (deferMap.flatMap KeyRoles.fragmentKeys) state
          ((executeResponseField schema resolvers variables fuel parentType source name
              fields path usages deferMap).run
            state) := by
    cases fuel with
    | zero =>
        simpa only [executeResponseField, StateT.run_pure, id_pure_eq, Completed,
          Completion.error]
          using Output.empty (inherited := deferMap.flatMap KeyRoles.fragmentKeys)
            (Nat.le_refl state)
    | succ fuel =>
        cases fields with
        | nil =>
            simpa only [executeResponseField, StateT.run_pure, id_pure_eq, Completed,
              Completion.error]
              using Output.empty (inherited := deferMap.flatMap KeyRoles.fragmentKeys)
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
      (fields : List ExecutableField) (value : ResolverValue ObjectRef)
      (path : ResponsePath) (usages : List Nat) (deferMap : DeferMap) (allowStream : Bool)
      (state : Nat) (hm : ∀ key ∈ deferMap.flatMap KeyRoles.fragmentKeys, key < state)
      : Completed (deferMap.flatMap KeyRoles.fragmentKeys) state
          ((completeValue schema resolvers variables fuel fieldType fields value path
              usages deferMap allowStream).run
            state) := by
    cases fuel with
    | zero =>
        simpa only [completeValue, StateT.run_pure, id_pure_eq, Completed,
          Completion.error]
          using Output.empty (inherited := deferMap.flatMap KeyRoles.fragmentKeys)
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
                  using Output.empty (inherited := deferMap.flatMap KeyRoles.fragmentKeys)
                    (Nat.le_refl state)
            | scalar scalar =>
                simp only [completeValue]; split <;> exact Output.empty _ (Nat.le_refl state)
            | list items =>
                simpa only [completeValue, StateT.run_pure, id_pure_eq, Completed,
                  Completion.error]
                  using Output.empty (inherited := deferMap.flatMap KeyRoles.fragmentKeys)
                    (Nat.le_refl state)
            | object runtimeType ref =>
                simp only [completeValue]
                split
                · exact Output.empty _ (Nat.le_refl state)
                · have hc := OwnerPaths.collectSubfields_supply schema variables runtimeType
                    (.object runtimeType ref) fields state
                  have h := executePlan_regions schema resolvers variables fuel runtimeType
                    (.object runtimeType ref) _ path usages deferMap _
                    (mapKeys_new_bound deferMap _ path _
                      (fun key hk => Nat.lt_of_lt_of_le (hm key hk) hc.1)
                      (fun usage hu => (hc.2 usage hu).2))
                  simp only [run_bind, StateT.run_pure, id_pure_eq]
                  apply output_catchNull
                  exact h.rebase hc.1 (mapKeys_new_root deferMap _ path state
                    (fun usage hu => (hc.2 usage hu).1))
        | list inner =>
            cases value with
            | null =>
                simpa only [completeValue, StateT.run_pure, id_pure_eq, Completed,
                  Completion.pure]
                  using Output.empty (inherited := deferMap.flatMap KeyRoles.fragmentKeys)
                    (Nat.le_refl state)
            | scalar scalar =>
                simpa only [completeValue, StateT.run_pure, id_pure_eq, Completed,
                  Completion.error]
                  using Output.empty (inherited := deferMap.flatMap KeyRoles.fragmentKeys)
                    (Nat.le_refl state)
            | object runtimeType ref =>
                simpa only [completeValue, StateT.run_pure, id_pure_eq, Completed,
                  Completion.error]
                  using Output.empty (inherited := deferMap.flatMap KeyRoles.fragmentKeys)
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
      (inner : TypeRef) (fields : List ExecutableField)
      (values : List (ResolverValue ObjectRef)) (path : ResponsePath) (usages : List Nat)
      (deferMap : DeferMap) (allowStream : Bool) (state : Nat)
      (hm : ∀ key ∈ deferMap.flatMap KeyRoles.fragmentKeys, key < state)
      : Completed (deferMap.flatMap KeyRoles.fragmentKeys) state
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
          simp only [freshExecutionKey, run_bind, StateT.run_get, StateT.run_set, StateT.run_pure, id_pure_eq]
          apply Output.append (output_catchNull _ _ hl) _ hm
          exact Output.stream _ {key := middle, path := path, label := usage.label} hr
  termination_by (fuel, 3, 0, 0)
  decreasing_by
    all_goals subst_vars; simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right

  theorem completeListValue_regions (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variables : VariableValues) (fuel : Nat) (itemType : TypeRef)
      (fields : List ExecutableField) (values : List (ResolverValue ObjectRef))
      (path : ResponsePath) (index : Nat) (usages : List Nat) (deferMap : DeferMap)
      (state : Nat) (hm : ∀ key ∈ deferMap.flatMap KeyRoles.fragmentKeys, key < state)
      : Completed (deferMap.flatMap KeyRoles.fragmentKeys) state
          ((completeListValue schema resolvers variables fuel itemType fields values path
              index usages deferMap).run
            state) := by
    cases values with
    | nil =>
        simpa only [completeListValue, StateT.run_pure, id_pure_eq, Completed,
          Completion.pure]
          using Output.empty (inherited := deferMap.flatMap KeyRoles.fragmentKeys)
            (Nat.le_refl state)
    | cons value rest =>
        have hl := completeValue_regions schema resolvers variables fuel itemType fields value
          (path ++ [.index index]) usages deferMap false state hm
        have hr := completeListValue_regions schema resolvers variables fuel itemType fields rest
          path (index + 1) usages deferMap _ (fun key hk => Nat.lt_of_lt_of_le (hm key hk) hl.monotone)
        simp only [completeListValue, run_bind, StateT.run_pure, id_pure_eq]
        exact output_combine List.cons _ _ hl hr hm
  termination_by (fuel, 2, sizeOf itemType, sizeOf values)
  decreasing_by
    all_goals subst_vars; simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right
    all_goals omega

  theorem completeStreamItems_regions (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variables : VariableValues) (fuel : Nat) (itemType : TypeRef)
      (fields : List ExecutableField) (values : List (ResolverValue ObjectRef))
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

theorem executeRoot_regions (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues) (fuel : Nat) (parentType : Name)
    (source : ResolverValue ObjectRef) (selections : List Selection) (state : Nat)
    : Completed [] state
        ((executeRootSelectionSetCore schema resolvers variables fuel parentType source
            selections).run
          state) := by
  have hc := OwnerPaths.collectFields_supply schema variables parentType source selections none state
  let collected := (collectFields schema variables parentType source selections none).run state
  have h := executePlan_regions schema resolvers variables fuel parentType source collected.1
    [] [] [] collected.2 (mapKeys_new_bound [] _ [] _ (by simp)
      (fun usage hu => (hc.2 usage hu).2))
  exact h.rebase hc.1 (mapKeys_new_root [] _ [] state (fun usage hu => (hc.2 usage hu).1))

theorem executeRoot_separated (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues) (fuel : Nat) (parentType : Name)
    (source : ResolverValue ObjectRef) (selections : List Selection) (state : Nat)
    : WorkSeparated
        ((executeRootSelectionSetCore schema resolvers variables fuel parentType source
            selections).run
          state).1.work :=
  (executeRoot_regions schema resolvers variables fuel parentType source selections
    state).separated

end GraphQL.IncrementalDelivery.Semantics.KeyRegions
