import Proofs.GraphQL.IncrementalDelivery.Semantics.KeyRoles

/-! Actual mixed execution assigns disjoint roles to stream and defer metadata keys.
Collection marks only fresh keys as defer keys; streaming marks its own fresh key.
All inherited fragment and ancestor keys lie below the allocation frontier.
-/

namespace GraphQL.IncrementalDelivery.Semantics.KeyRoles

open GraphQL.IncrementalDelivery.Execution
open GeneralScheduling

attribute [local simp] id_pure_eq id_bind_eq id_map_eq run_bind run_map

mutual
  theorem executePlan_roles (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variables : VariableValues) (fuel : Nat) (parentType : Name)
      (source : ResolverValue ObjectRef) (collection : FieldCollection)
      (path : ResponsePath) (usages : List Nat) (deferMap : DeferMap) (roles : Assignment)
      (state : Nat)
      (hm : MapAt roles state (getNewDeferMap collection.newDeferUsages path deferMap))
      : Completed roles state
          ((executeExecutionPlan schema resolvers variables fuel parentType source
              collection.newDeferUsages (buildExecutionPlan collection.fields usages) path
              usages deferMap).run
            state) := by
    obtain ⟨hle, middle, he, hw⟩ := executeCollectedFields_roles schema resolvers variables fuel parentType source
      _ path usages _ roles state hm
    simp only [executeExecutionPlan, run_bind]
    split
    · exact ⟨hle, middle, he, hw⟩
    · obtain ⟨hlt, final, het, hwt⟩ := collectExecutionGroups_roles schema resolvers variables fuel parentType source
        _ path _ middle _ (hm.extend he hle)
      simp only [run_bind, StateT.run_pure, id_pure_eq]
      exact ⟨Nat.le_trans hle hlt, final, he.trans het hle,
        workAt_combine (hw.extend het hlt) hwt⟩
  termination_by (fuel, 6, 0, 0)
  decreasing_by
    all_goals simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right

  theorem collectExecutionGroups_roles (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variables : VariableValues) (fuel : Nat) (parentType : Name)
      (source : ResolverValue ObjectRef)
      (partitions : List (List Nat × CollectedFieldsMap)) (path : ResponsePath)
      (deferMap : DeferMap) (roles : Assignment) (state : Nat)
      (hm : MapAt roles state deferMap)
      : let output :=
          (collectExecutionGroups schema resolvers variables fuel parentType source
            partitions path deferMap).run
            state
        Output roles state output.1 output.2 := by
    cases partitions with
    | nil =>
        simpa only [collectExecutionGroups, StateT.run_pure, id_pure_eq] using output_empty roles state
    | cons partition rest =>
        rcases partition with ⟨usages, groups⟩
        obtain ⟨hle, middle, he, hw⟩ := executeCollectedFields_roles schema resolvers variables fuel parentType source
          groups path usages deferMap roles state hm
        obtain ⟨hlt, final, het, hwt⟩ := collectExecutionGroups_roles schema resolvers variables fuel parentType source
          rest path deferMap middle _ (hm.extend he hle)
        have hd := workAt_deferred final _ deferMap usages path
          ((executeCollectedFields schema resolvers variables fuel parentType source groups path usages deferMap).run state).1.result
          _ ((hm.extend he hle).extend het hlt) (hw.extend het hlt)
        simp only [collectExecutionGroups, executeExecutionGroup, run_bind, StateT.run_pure, id_pure_eq]
        exact ⟨Nat.le_trans hle hlt, final, he.trans het hle,
          workAt_combine hd hwt⟩
  termination_by (fuel, 5, 0, sizeOf partitions)
  decreasing_by
    all_goals subst_vars; simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right
    all_goals omega

  theorem executeCollectedFields_roles (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variables : VariableValues) (fuel : Nat) (parentType : Name)
      (source : ResolverValue ObjectRef) (groups : CollectedFieldsMap)
      (path : ResponsePath) (usages : List Nat) (deferMap : DeferMap) (roles : Assignment)
      (state : Nat) (hm : MapAt roles state deferMap)
      : Completed roles state
          ((executeCollectedFields schema resolvers variables fuel parentType source
              groups path usages deferMap).run
            state) := by
    cases groups with
    | nil =>
        simpa only [executeCollectedFields_nil, StateT.run_pure, id_pure_eq, Completed,
          Completion.pure]
          using output_empty roles state
    | cons group rest =>
        rcases group with ⟨name, fields⟩
        obtain ⟨hle, middle, he, hw⟩ := executeResponseField_roles schema resolvers
          variables fuel parentType source
          name fields path usages deferMap roles state hm
        obtain ⟨hlt, final, het, hwt⟩ := executeCollectedFields_roles schema resolvers variables fuel parentType source
          rest path usages deferMap middle _ (hm.extend he hle)
        simp only [executeCollectedFields_cons, run_bind, StateT.run_pure, id_pure_eq]
        exact ⟨Nat.le_trans hle hlt, final, he.trans het hle,
          workAt_completionCombine final _ List.append _ _ (hw.extend het hlt) hwt⟩
  termination_by (fuel, 4, 0, sizeOf groups)
  decreasing_by
    all_goals subst_vars; simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right
    all_goals omega

  theorem executeResponseField_roles (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variables : VariableValues) (fuel : Nat) (parentType : Name)
      (source : ResolverValue ObjectRef) (name : Name) (fields : List ExecutableField)
      (path : ResponsePath) (usages : List Nat) (deferMap : DeferMap) (roles : Assignment)
      (state : Nat) (hm : MapAt roles state deferMap)
      : Completed roles state
          ((executeResponseField schema resolvers variables fuel parentType source name
              fields path usages deferMap).run
            state) := by
    cases fuel with
    | zero =>
        simpa only [executeResponseField, StateT.run_pure, id_pure_eq, Completed,
          Completion.error]
          using output_empty roles state
    | succ fuel =>
        cases fields with
        | nil =>
            simpa only [executeResponseField, StateT.run_pure, id_pure_eq, Completed,
              Completion.error]
              using output_empty roles state
        | cons field rest =>
            simp only [executeResponseField]
            split
            · exact output_empty roles state
            · split
              · exact output_empty roles state
              · split
                · exact output_empty roles state
                · obtain ⟨hle, next, he, hw⟩ := completeValue_roles schema resolvers variables fuel _ _ _
                    (path ++ [.field name]) usages deferMap true roles state hm
                  simp only [run_bind, StateT.run_pure, id_pure_eq]
                  exact ⟨hle, next, he, workAt_map next _ _ _ hw⟩
  termination_by (fuel, 3, 0, sizeOf fields)
  decreasing_by
    all_goals subst_vars; simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right

  theorem completeValue_roles (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variables : VariableValues) (fuel : Nat) (fieldType : TypeRef)
      (fields : List ExecutableField) (value : ResolverValue ObjectRef)
      (path : ResponsePath) (usages : List Nat) (deferMap : DeferMap) (allowStream : Bool)
      (roles : Assignment) (state : Nat) (hm : MapAt roles state deferMap)
      : Completed roles state
          ((completeValue schema resolvers variables fuel fieldType fields value path
              usages deferMap allowStream).run
            state) := by
    cases fuel with
    | zero =>
        simpa only [completeValue, StateT.run_pure, id_pure_eq, Completed,
          Completion.error]
          using output_empty roles state
    | succ fuel =>
        cases fieldType with
        | nonNull inner =>
            obtain ⟨hle, next, he, hw⟩ := completeValue_roles schema resolvers variables (fuel + 1) inner fields
              value path usages deferMap allowStream roles state hm
            simp only [completeValue, run_bind, StateT.run_pure, id_pure_eq]
            exact ⟨hle, next, he, workAt_nonNull next _ _ hw⟩
        | named parentType =>
            cases value with
            | null =>
                simpa only [completeValue, StateT.run_pure, id_pure_eq, Completed,
                  Completion.pure]
                  using output_empty roles state
            | scalar scalar =>
                simp only [completeValue]; split <;> exact output_empty roles state
            | list items =>
                simpa only [completeValue, StateT.run_pure, id_pure_eq, Completed,
                  Completion.error]
                  using output_empty roles state
            | object runtimeType ref =>
                simp only [completeValue]
                split
                · exact output_empty roles state
                · have hc := OwnerPaths.collectSubfields_supply schema variables runtimeType (.object runtimeType ref) fields state
                  have hm' := mapAt_collection hm hc.1 _ hc.2 path
                  obtain ⟨hle, next, he, hw⟩ := executePlan_roles schema resolvers variables fuel runtimeType
                    (.object runtimeType ref) _ path usages deferMap (markDefer roles state) _ hm'
                  simp only [run_bind, StateT.run_pure, id_pure_eq]
                  exact ⟨Nat.le_trans hc.1 hle, next, (markDefer_extends roles state).trans he hc.1,
                    workAt_catchNull next _ _ _ hw⟩
        | list inner =>
            cases value with
            | null =>
                simpa only [completeValue, StateT.run_pure, id_pure_eq, Completed,
                  Completion.pure]
                  using output_empty roles state
            | scalar scalar =>
                simpa only [completeValue, StateT.run_pure, id_pure_eq, Completed,
                  Completion.error]
                  using output_empty roles state
            | object runtimeType ref =>
                simpa only [completeValue, StateT.run_pure, id_pure_eq, Completed,
                  Completion.error]
                  using output_empty roles state
            | list items =>
                simpa only [completeValue] using completeListValueWithStream_roles schema
                  resolvers variables fuel inner
                  fields items path usages deferMap allowStream roles state hm
  termination_by (fuel, 1, sizeOf fieldType, 0)
  decreasing_by
    all_goals subst_vars; simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right

  theorem completeListValueWithStream_roles (schema : Schema)
      (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
      (inner : TypeRef) (fields : List ExecutableField)
      (values : List (ResolverValue ObjectRef)) (path : ResponsePath) (usages : List Nat)
      (deferMap : DeferMap) (allowStream : Bool) (roles : Assignment) (state : Nat)
      (hm : MapAt roles state deferMap)
      : Completed roles state
          ((completeListValueWithStream schema resolvers variables fuel inner fields
              values path usages deferMap allowStream).run
            state) := by
    unfold completeListValueWithStream
    dsimp only
    split
    · exact output_empty roles state
    · obtain ⟨hle, next, he, hw⟩ := completeListValue_roles schema resolvers variables
        fuel inner fields values
        path 0 usages deferMap roles state hm
      simp only [run_bind, StateT.run_pure, id_pure_eq]
      exact ⟨hle, next, he, workAt_catchNull next _ _ _ hw⟩
    · rename_i usage _
      obtain ⟨hle, middle, he, hw⟩ := completeListValue_roles schema resolvers variables
        fuel inner fields
        (values.take usage.initialCount) path 0 usages deferMap roles state hm
      simp only [run_bind]
      split
      · exact ⟨hle, middle, he, workAt_catchNull middle _ _ _ hw⟩
      · split
        · exact ⟨hle, middle, he, workAt_catchNull middle _ _ _ hw⟩
        · let frontier := ((completeListValue schema resolvers variables fuel inner fields
            (values.take usage.initialCount) path 0 usages deferMap).run state).2
          obtain ⟨hlt, final, het, hitems⟩ := completeStreamItems_roles schema resolvers variables fuel inner
            (fields.map (fun field => { field with deferUsage := none })) (values.drop usage.initialCount)
            path usage.initialCount (markStream middle frontier) (frontier + 1)
          have heall := (markStream_extends middle frontier).trans het (Nat.le_succ frontier)
          have hrole : final frontier = true := (het frontier (Nat.lt_succ_self _)).trans (by simp [markStream])
          simp only [freshExecutionKey, run_bind, StateT.run_get, StateT.run_set, StateT.run_pure, id_pure_eq]
          refine ⟨by dsimp only [frontier] at *; omega, final, he.trans heall hle, ?_⟩
          apply workAt_combine (workAt_catchNull final _ _ _
            (hw.extend heall (by dsimp only [frontier] at *; omega)))
          exact workAt_stream final _ _ _ ⟨by dsimp only [frontier] at *; omega, hrole⟩ hitems
  termination_by (fuel, 3, 0, 0)
  decreasing_by
    all_goals subst_vars; simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right

  theorem completeListValue_roles (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variables : VariableValues) (fuel : Nat) (itemType : TypeRef)
      (fields : List ExecutableField) (values : List (ResolverValue ObjectRef))
      (path : ResponsePath) (index : Nat) (usages : List Nat) (deferMap : DeferMap)
      (roles : Assignment) (state : Nat) (hm : MapAt roles state deferMap)
      : Completed roles state
          ((completeListValue schema resolvers variables fuel itemType fields values path
              index usages deferMap).run
            state) := by
    cases values with
    | nil =>
        simpa only [completeListValue, StateT.run_pure, id_pure_eq, Completed,
          Completion.pure]
          using output_empty roles state
    | cons value rest =>
        obtain ⟨hle, middle, he, hw⟩ := completeValue_roles schema resolvers variables fuel itemType fields value
          (path ++ [.index index]) usages deferMap false roles state hm
        obtain ⟨hlt, final, het, hwt⟩ := completeListValue_roles schema resolvers
          variables fuel itemType fields rest
          path (index + 1) usages deferMap middle _ (hm.extend he hle)
        simp only [completeListValue, run_bind, StateT.run_pure, id_pure_eq]
        exact ⟨Nat.le_trans hle hlt, final, he.trans het hle,
          workAt_completionCombine final _ List.cons _ _ (hw.extend het hlt) hwt⟩
  termination_by (fuel, 2, sizeOf itemType, sizeOf values)
  decreasing_by
    all_goals subst_vars; simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right
    all_goals omega

  theorem completeStreamItems_roles (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variables : VariableValues) (fuel : Nat) (itemType : TypeRef)
      (fields : List ExecutableField) (values : List (ResolverValue ObjectRef))
      (path : ResponsePath) (index : Nat) (roles : Assignment) (state : Nat)
      : let output :=
          (completeStreamItems schema resolvers variables fuel itemType fields values path
            index).run
            state
        state ≤ output.2
        ∧ ∃ next,
            Extends state roles next
            ∧ ∀ item ∈ output.1, WorkAt next output.2 item.2 := by
    cases values with
    | nil =>
        simp only [completeStreamItems, StateT.run_pure, id_pure_eq]
        exact ⟨Nat.le_refl _, roles, Extends.refl _ _, by simp⟩
    | cons value rest =>
        obtain ⟨hle, middle, he, hw⟩ := completeValue_roles schema resolvers variables fuel itemType fields value
          (path ++ [.index index]) [] [] false roles state (by simp [MapAt, KeysAt])
        simp only [completeStreamItems, run_bind]
        split
        · refine ⟨hle, middle, he, ?_⟩
          intro item hi
          obtain rfl := List.mem_singleton.mp hi
          exact workAt_empty _ _
        · obtain ⟨hlt, final, het, htail⟩ := completeStreamItems_roles schema resolvers variables fuel itemType fields rest
            path (index + 1) middle _
          simp only [run_bind, StateT.run_pure, id_pure_eq]
          refine ⟨Nat.le_trans hle hlt, final, he.trans het hle, ?_⟩
          intro item hi
          rcases List.mem_cons.mp hi with rfl | hi
          · exact hw.extend het hlt
          · exact htail item hi
  termination_by (fuel, 2, sizeOf itemType, sizeOf values)
  decreasing_by
    all_goals subst_vars; simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right
    all_goals omega
end

theorem executeRoot_rolesAt (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues) (fuel : Nat) (parentType : Name)
    (source : ResolverValue ObjectRef) (selections : List Selection) (state : Nat)
    : let output :=
        (executeRootSelectionSetCore schema resolvers variables fuel parentType source
          selections).run
          state
      state ≤ output.2 ∧ ∃ roles, WorkAt roles output.2 output.1.work := by
  have hc := OwnerPaths.collectFields_supply schema variables parentType source selections none state
  have hm := mapAt_collection (roles := fun _ => false) (deferMap := []) (by simp [MapAt, KeysAt]) hc.1 _ hc.2 []
  obtain ⟨hle, roles, _, hw⟩ := executePlan_roles schema resolvers variables fuel parentType source
    _ [] [] [] (markDefer (fun _ => false) state) _ hm
  exact ⟨Nat.le_trans hc.1 hle, roles, hw⟩

theorem executeRoot_roles (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues) (fuel : Nat) (parentType : Name)
    (source : ResolverValue ObjectRef) (selections : List Selection) (state : Nat)
    : ∃ roles,
        WorkRoles roles
          ((executeRootSelectionSetCore schema resolvers variables fuel parentType source
              selections).run
            state).1.work := by
  obtain ⟨_, roles, hw⟩ := executeRoot_rolesAt schema resolvers variables fuel parentType source selections state
  exact ⟨roles, hw.roles⟩

theorem executeRoot_stream_defer_separate (schema : Schema)
    (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
    (parentType : Name) (source : ResolverValue ObjectRef) (selections : List Selection)
    (state key : Nat)
    (hs
      : key
        ∈ streamAllocationKeys
            ((executeRootSelectionSetCore schema resolvers variables fuel parentType
                source selections).run
              state).1.work)
    : key
      ∉ deferMetadataKeys
          ((executeRootSelectionSetCore schema resolvers variables fuel parentType source
              selections).run
            state).1.work := by
  obtain ⟨_, _, hw⟩ := executeRoot_rolesAt schema resolvers variables fuel parentType source selections state
  exact hw.separate hs

end GraphQL.IncrementalDelivery.Semantics.KeyRoles
