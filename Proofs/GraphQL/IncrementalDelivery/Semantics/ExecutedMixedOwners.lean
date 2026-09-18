import Proofs.GraphQL.IncrementalDelivery.Semantics.MixedOwnerMetadata
import Proofs.GraphQL.IncrementalDelivery.Semantics.CollectedSupply

/-! Actual mixed execution assigns each allocated key one absolute attachment path,
including all work in streamed items. No success or directive restriction is needed.
-/

namespace GraphQL.IncrementalDelivery.Semantics.MixedOwnerPaths

open GraphQL.IncrementalDelivery.Execution
open OwnerPaths

attribute [local simp] id_pure_eq id_bind_eq id_map_eq run_bind run_map

mutual
  theorem executePlan_owners (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variables : VariableValues) (fuel : Nat) (parentType : Name)
      (source : ResolverValue ObjectRef) (collection : FieldCollection)
      (path : ResponsePath) (usages : List Nat) (deferMap : DeferMap)
      (paths : Assignment) (state : Nat)
      (hm
        : MapAt paths state path (getNewDeferMap collection.newDeferUsages path deferMap))
      : Completed paths state
          ((executeExecutionPlan schema resolvers variables fuel parentType source
              collection.newDeferUsages (buildExecutionPlan collection.fields usages) path
              usages deferMap).run
            state) := by
    obtain ⟨hle, middle, he, hw⟩ := executeCollectedFields_owners schema resolvers variables fuel
      parentType source _ path usages _ paths state hm
    simp only [executeExecutionPlan, run_bind]
    split
    · exact ⟨hle, middle, he, hw⟩
    · obtain ⟨hlt, final, het, hwt⟩ := collectExecutionGroups_owners schema resolvers variables fuel
        parentType source _ path _ middle _ (hm.extend he hle)
      simp only [run_bind, StateT.run_pure, id_pure_eq]
      refine ⟨Nat.le_trans hle hlt, final, he.trans het hle, ?_⟩
      rw [WorkAt]
      exact ⟨hw.extend het hlt, hwt⟩
  termination_by (fuel, 6, 0, 0)
  decreasing_by
    all_goals simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right

  theorem collectExecutionGroups_owners (schema : Schema)
      (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
      (parentType : Name) (source : ResolverValue ObjectRef)
      (partitions : List (List Nat × CollectedFieldsMap)) (path : ResponsePath)
      (deferMap : DeferMap) (paths : Assignment) (state : Nat)
      (hm : MapAt paths state path deferMap)
      : let output :=
          (collectExecutionGroups schema resolvers variables fuel parentType
            source partitions path deferMap).run
            state
        Output paths state output.1 output.2 := by
    cases partitions with
    | nil =>
        simpa only [collectExecutionGroups, StateT.run_pure, id_pure_eq] using output_empty paths state
    | cons partition rest =>
        rcases partition with ⟨usages, groups⟩
        obtain ⟨hle, middle, he, hw⟩ := executeCollectedFields_owners schema resolvers variables fuel
          parentType source groups path usages deferMap paths state hm
        have hm' := hm.extend he hle
        obtain ⟨hlt, final, het, hwt⟩ := collectExecutionGroups_owners schema resolvers variables fuel
          parentType source rest path deferMap middle _ hm'
        simp only [collectExecutionGroups, executeExecutionGroup, run_bind, StateT.run_pure, id_pure_eq]
        refine ⟨Nat.le_trans hle hlt, final, he.trans het hle, ?_⟩
        simp only [WorkAt]
        exact ⟨⟨mapAt_filterMap (hm'.extend het hlt) usages, hw.extend het hlt⟩, hwt⟩
  termination_by (fuel, 5, 0, sizeOf partitions)
  decreasing_by
    all_goals subst_vars; simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right
    all_goals omega

  theorem executeCollectedFields_owners (schema : Schema)
      (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
      (parentType : Name) (source : ResolverValue ObjectRef) (groups : CollectedFieldsMap)
      (path : ResponsePath) (usages : List Nat) (deferMap : DeferMap) (paths : Assignment)
      (state : Nat) (hm : MapAt paths state path deferMap)
      : Completed paths state
          ((executeCollectedFields schema resolvers variables fuel parentType source
              groups path usages deferMap).run
            state) := by
    cases groups with
    | nil =>
        simpa only [executeCollectedFields_nil, StateT.run_pure, id_pure_eq, Completed,
        Completion.pure] using output_empty paths state
    | cons group rest =>
        rcases group with ⟨name, fields⟩
        obtain ⟨hle, middle, he, hw⟩ := executeResponseField_owners schema resolvers variables fuel
          parentType source name fields path usages deferMap paths state hm
        obtain ⟨hlt, final, het, hwt⟩ := executeCollectedFields_owners schema resolvers variables fuel
          parentType source rest path usages deferMap middle _ (hm.extend he hle)
        simp only [executeCollectedFields_cons, run_bind, StateT.run_pure, id_pure_eq]
        exact ⟨Nat.le_trans hle hlt, final, he.trans het hle,
          workAt_combine final _ List.append _ _ (hw.extend het hlt) hwt⟩
  termination_by (fuel, 4, 0, sizeOf groups)
  decreasing_by
    all_goals subst_vars; simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right
    all_goals omega

  theorem executeResponseField_owners (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variables : VariableValues) (fuel : Nat) (parentType : Name)
      (source : ResolverValue ObjectRef) (name : Name) (fields : List ExecutableField)
      (path : ResponsePath) (usages : List Nat) (deferMap : DeferMap)
      (paths : Assignment) (state : Nat) (hm : MapAt paths state path deferMap)
      : Completed paths state
          ((executeResponseField schema resolvers variables fuel parentType source name
              fields path usages deferMap).run
            state) := by
    cases fuel with
    | zero => simpa only [executeResponseField, StateT.run_pure, id_pure_eq, Completed,
        Completion.error] using output_empty paths state
    | succ fuel =>
        cases fields with
        | nil => simpa only [executeResponseField, StateT.run_pure, id_pure_eq, Completed,
            Completion.error] using output_empty paths state
        | cons field rest =>
            simp only [executeResponseField]
            split
            · exact output_empty paths state
            · split
              · exact output_empty paths state
              · split
                · exact output_empty paths state
                · obtain ⟨hle, next, he, hw⟩ := completeValue_owners schema resolvers variables fuel _ _ _
                    (path ++ [.field name]) usages deferMap true paths state (hm.below ⟨_, rfl⟩)
                  simp only [run_bind, StateT.run_pure, id_pure_eq]
                  exact ⟨hle, next, he, workAt_map next _ _ _ hw⟩
  termination_by (fuel, 3, 0, sizeOf fields)
  decreasing_by
    all_goals subst_vars; simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right

  theorem completeValue_owners (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variables : VariableValues) (fuel : Nat) (fieldType : TypeRef)
      (fields : List ExecutableField) (value : ResolverValue ObjectRef)
      (path : ResponsePath) (usages : List Nat) (deferMap : DeferMap)
      (allowStream : Bool) (paths : Assignment) (state : Nat)
      (hm : MapAt paths state path deferMap)
      : Completed paths state
          ((completeValue schema resolvers variables fuel fieldType fields value path
              usages deferMap allowStream).run
            state) := by
    cases fuel with
    | zero => simpa only [completeValue, StateT.run_pure, id_pure_eq, Completed,
        Completion.error] using output_empty paths state
    | succ fuel =>
        cases fieldType with
        | nonNull inner =>
            obtain ⟨hle, next, he, hw⟩ := completeValue_owners schema resolvers variables (fuel + 1)
              inner fields value path usages deferMap allowStream paths state hm
            simp only [completeValue, run_bind, StateT.run_pure, id_pure_eq]
            exact ⟨hle, next, he, workAt_nonNull next _ _ hw⟩
        | named parentType =>
            cases value with
            | null => simpa only [completeValue, StateT.run_pure, id_pure_eq, Completed,
                Completion.pure] using output_empty paths state
            | scalar scalar =>
                simp only [completeValue]; split <;> exact output_empty paths state
            | list items =>
                simpa only [completeValue, StateT.run_pure, id_pure_eq, Completed,
                Completion.error] using output_empty paths state
            | object runtimeType ref =>
                simp only [completeValue]
                split
                · exact output_empty paths state
                · have hs := collectSubfields_supply schema variables runtimeType (.object runtimeType ref) fields state
                  obtain ⟨he, hn⟩ := mapAt_new paths state _ path deferMap _ hm hs.1 hs.2
                  obtain ⟨hle, next, he', hw⟩ := executePlan_owners schema resolvers variables fuel
                    runtimeType (.object runtimeType ref) _ path usages deferMap _ _ hn
                  simp only [run_bind, StateT.run_pure, id_pure_eq]
                  exact ⟨Nat.le_trans hs.1 hle, next, he.trans he' hs.1, workAt_catchNull next _ _ _ hw⟩
        | list inner =>
            cases value with
            | null => simpa only [completeValue, StateT.run_pure, id_pure_eq, Completed,
                Completion.pure] using output_empty paths state
            | scalar scalar =>
                simpa only [completeValue, StateT.run_pure, id_pure_eq, Completed,
                Completion.error] using output_empty paths state
            | object runtimeType ref =>
                simpa only [completeValue, StateT.run_pure, id_pure_eq, Completed,
                Completion.error] using output_empty paths state
            | list items =>
                simpa only [completeValue] using completeListValueWithStream_owners schema
                  resolvers variables
                  fuel inner fields items path usages deferMap allowStream paths state hm
  termination_by (fuel, 1, sizeOf fieldType, 0)
  decreasing_by
    all_goals subst_vars; simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right

  theorem completeListValueWithStream_owners (schema : Schema)
      (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
      (inner : TypeRef) (fields : List ExecutableField)
      (values : List (ResolverValue ObjectRef)) (path : ResponsePath) (usages : List Nat)
      (deferMap : DeferMap) (allowStream : Bool) (paths : Assignment) (state : Nat)
      (hm : MapAt paths state path deferMap)
      : Completed paths state
          ((completeListValueWithStream schema resolvers variables fuel inner fields
              values path usages deferMap allowStream).run
            state) := by
    unfold completeListValueWithStream
    dsimp only
    split
    · exact output_empty paths state
    · obtain ⟨hle, next, he, hw⟩ := completeListValue_owners schema resolvers variables fuel inner
        fields values path 0 usages deferMap paths state hm
      simp only [run_bind, StateT.run_pure, id_pure_eq]
      exact ⟨hle, next, he, workAt_catchNull next _ _ _ hw⟩
    · rename_i usage _
      obtain ⟨hle, middle, he, hw⟩ := completeListValue_owners schema resolvers variables fuel inner
        fields (values.take usage.initialCount) path 0 usages deferMap paths state hm
      simp only [run_bind]
      split
      · exact ⟨hle, middle, he, workAt_catchNull middle _ _ _ hw⟩
      · split
        · exact ⟨hle, middle, he, workAt_catchNull middle _ _ _ hw⟩
        · let mid := ((completeListValue schema resolvers variables fuel inner fields
            (values.take usage.initialCount) path 0 usages deferMap).run state).2
          let node : DeliveryNode := {key := mid, path, label := usage.label}
          obtain ⟨hfresh, hnode⟩ := assigned_fresh middle mid node rfl
          obtain ⟨hlt, final, het, hitems⟩ := completeStreamItems_owners schema resolvers variables fuel
            inner (fields.map (fun field => {field with deferUsage := none}))
            (values.drop usage.initialCount) path usage.initialCount
            (fun key => if key = mid then path else middle key) (mid + 1)
          dsimp only [mid] at hlt
          simp only [freshExecutionKey, run_bind, StateT.run_get, StateT.run_set,
            StateT.run_pure, id_pure_eq]
          refine ⟨by omega, final, he.trans (hfresh.trans het (by omega)) hle, ?_⟩
          rw [WorkAt]
          refine ⟨(workAt_catchNull middle _ _ _ hw).extend (hfresh.trans het (by omega)) (by omega), ?_⟩
          rw [WorkAt]
          exact ⟨hnode.extend het hlt, hitems⟩
  termination_by (fuel, 3, 0, 0)
  decreasing_by
    all_goals subst_vars; simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right

  theorem completeListValue_owners (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variables : VariableValues) (fuel : Nat) (itemType : TypeRef)
      (fields : List ExecutableField) (values : List (ResolverValue ObjectRef))
      (path : ResponsePath) (index : Nat) (usages : List Nat) (deferMap : DeferMap)
      (paths : Assignment) (state : Nat) (hm : MapAt paths state path deferMap)
      : Completed paths state
          ((completeListValue schema resolvers variables fuel itemType fields values path
              index usages deferMap).run
            state) := by
    cases values with
    | nil => simpa only [completeListValue, StateT.run_pure, id_pure_eq, Completed,
        Completion.pure] using output_empty paths state
    | cons value rest =>
        obtain ⟨hle, middle, he, hw⟩ := completeValue_owners schema resolvers variables fuel itemType fields
          value (path ++ [.index index]) usages deferMap false paths state (hm.below ⟨_, rfl⟩)
        obtain ⟨hlt, final, het, hwt⟩ := completeListValue_owners schema resolvers variables fuel
          itemType fields rest path (index + 1) usages deferMap middle _ (hm.extend he hle)
        simp only [completeListValue, run_bind, StateT.run_pure, id_pure_eq]
        exact ⟨Nat.le_trans hle hlt, final, he.trans het hle,
          workAt_combine final _ List.cons _ _ (hw.extend het hlt) hwt⟩
  termination_by (fuel, 2, sizeOf itemType, sizeOf values)
  decreasing_by
    all_goals subst_vars; simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right
    all_goals omega

  theorem completeStreamItems_owners (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variables : VariableValues) (fuel : Nat) (itemType : TypeRef)
      (fields : List ExecutableField) (values : List (ResolverValue ObjectRef))
      (path : ResponsePath) (index : Nat) (paths : Assignment) (state : Nat)
      : ItemsOutput paths state
          ((completeStreamItems schema resolvers variables fuel itemType fields values
              path index).run
            state) := by
    cases values with
    | nil =>
        simp only [completeStreamItems, StateT.run_pure, id_pure_eq]
        exact ⟨Nat.le_refl _, paths, Extends.refl _ _, by simp [ItemsAt]⟩
    | cons value rest =>
        obtain ⟨hle, middle, he, hw⟩ := completeValue_owners schema resolvers variables fuel itemType
          fields value (path ++ [.index index]) [] [] false paths state (by simp [MapAt, mapNodes])
        simp only [completeStreamItems, run_bind]
        split
        · exact ⟨hle, middle, he, by simp [ItemsAt, WorkAt]⟩
        · obtain ⟨hlt, final, het, hitems⟩ := completeStreamItems_owners schema resolvers variables fuel
            itemType fields rest path (index + 1) middle
            ((completeValue schema resolvers variables fuel itemType fields value
              (path ++ [.index index]) [] [] false).run state).2
          simp only [run_bind, StateT.run_pure, id_pure_eq]
          refine ⟨Nat.le_trans hle hlt, final, he.trans het hle, ?_⟩
          intro item hi
          rcases List.mem_cons.mp hi with rfl | hi
          · exact hw.extend het hlt
          · exact hitems item hi
  termination_by (fuel, 2, sizeOf itemType, sizeOf values)
  decreasing_by
    all_goals subst_vars; simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right
    all_goals omega
end

theorem executeRoot_owners (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues) (fuel : Nat) (parentType : Name)
    (source : ResolverValue ObjectRef) (selections : List Selection) (state : Nat)
    : ∃ paths,
        WorkAt paths
          ((executeRootSelectionSetCore schema resolvers variables fuel parentType source
              selections).run
            state).2
          ((executeRootSelectionSetCore schema resolvers variables fuel parentType source
              selections).run
            state).1.work := by
  have hs := collectFields_supply schema variables parentType source selections none state
  obtain ⟨_, hm⟩ := mapAt_new (fun _ => []) state _ [] [] _ (by simp [MapAt, mapNodes]) hs.1 hs.2
  obtain ⟨_, paths, _, hw⟩ := executePlan_owners schema resolvers variables fuel parentType
    source _ [] [] [] _ _ hm
  exact ⟨paths, hw⟩

end GraphQL.IncrementalDelivery.Semantics.MixedOwnerPaths
