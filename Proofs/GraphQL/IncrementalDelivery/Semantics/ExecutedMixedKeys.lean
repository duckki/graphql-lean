import Proofs.GraphQL.IncrementalDelivery.Semantics.MixedWorkKeys

/-! Arbitrary execution produces bounded, nonempty-key mixed delivery work.
The proof follows fresh state allocation through all completion branches. Stream
items reset defer context and therefore allocate strictly after their stream owner.
-/

namespace GraphQL.IncrementalDelivery.Semantics.MixedKeys

open GraphQL.IncrementalDelivery.Execution
open Ancestry

attribute [local simp] id_pure_eq id_bind_eq id_map_eq run_bind run_map

mutual
  theorem executePlan_keys (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variables : VariableValues) (fuel : Nat) (parentType : Name)
      (source : ResolverValue ObjectRef) (collection : FieldCollection)
      (path : ResponsePath) (usages : List Nat) (deferMap : DeferMap)
      (parents : Assignment) (lower state : Nat) (hls : lower ≤ state)
      (hv : Valid parents state)
      (hm : MapAt parents state (getNewDeferMap collection.newDeferUsages path deferMap))
      (hl : MapLower lower (getNewDeferMap collection.newDeferUsages path deferMap))
      (hk
        : GroupsSatisfy
            (fun field =>
              OptionalUsageAt parents state
                (getNewDeferMap collection.newDeferUsages path deferMap) field.deferUsage)
            collection.fields)
      (hn : GroupsNonempty collection.fields)
      (hu : GroupsUnder usages collection.fields)
      : Completed parents lower state
          ((executeExecutionPlan schema resolvers variables fuel parentType source
              collection.newDeferUsages (buildExecutionPlan collection.fields usages) path
              usages deferMap).run
            state) := by
    have hpk := buildExecutionPlan_preserves_property _ collection.fields usages hk
    have hpu := buildExecutionPlan_preserves_property _ collection.fields usages hu
    have hpp := buildExecutionPlan_partitionsAt parents state _ usages collection.fields hv hm hk hn
      hu
    obtain ⟨hle, middle, he, hmv, hw⟩ := executeCollectedFields_keys schema resolvers variables fuel
      parentType source _ path usages _ parents lower state hls hv hm hl hpk.1 hpu.1
    simp only [executeExecutionPlan, run_bind]
    split
    · exact ⟨hle, middle, he, hmv, hw⟩
    · obtain ⟨hlt, final, het, hfv, hwt⟩ := collectExecutionGroups_keys schema resolvers variables fuel
        parentType source _ path _ middle lower _ (Nat.le_trans hls hle) hmv (hm.extend he hle) hl
        (fun p hp => groupsKnown_extend (hpk.2 p hp) he hle)
        (fun p hp => ⟨(hpp p hp).1, (hpp p hp).2.1, (hpp p hp).2.2.1⟩)
      simp only [run_bind, StateT.run_pure, id_pure_eq]
      exact ⟨Nat.le_trans hle hlt, final, he.trans het hle, hfv,
        workAt_combine (hw.extend het hlt) hwt⟩
  termination_by (fuel, 6, 0, 0)
  decreasing_by
    all_goals simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right

  theorem collectExecutionGroups_keys (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variables : VariableValues) (fuel : Nat) (parentType : Name)
      (source : ResolverValue ObjectRef)
      (partitions : List (List Nat × CollectedFieldsMap)) (path : ResponsePath)
      (deferMap : DeferMap) (parents : Assignment) (lower state : Nat)
      (hls : lower ≤ state) (hv : Valid parents state) (hm : MapAt parents state deferMap)
      (hl : MapLower lower deferMap)
      (hk
        : ∀ partition ∈ partitions,
            GroupsSatisfy
              (fun field => OptionalUsageAt parents state deferMap field.deferUsage)
              partition.2)
      (hp
        : ∀ partition ∈ partitions,
            partition.1 ≠ []
            ∧ partition.1.Subset (mapKeys deferMap)
            ∧ GroupsUnder partition.1 partition.2)
      : Output parents lower state
          ((collectExecutionGroups schema resolvers variables fuel parentType source
              partitions path deferMap).run
            state).1
          ((collectExecutionGroups schema resolvers variables fuel parentType source
              partitions path deferMap).run
            state).2 := by
    cases partitions with
    | nil =>
        simpa only [collectExecutionGroups, StateT.run_pure, id_pure_eq] using output_empty parents lower state hv
    | cons partition rest =>
        rcases partition with ⟨usages, groups⟩
        obtain ⟨hle, middle, he, hmv, hw⟩ := executeCollectedFields_keys schema resolvers variables fuel
          parentType source groups path usages deferMap parents lower state hls hv hm hl
          (hk (usages, groups) (by simp)) (hp (usages, groups) (by simp)).2.2
        obtain ⟨hlt, final, het, hfv, hwt⟩ := collectExecutionGroups_keys schema resolvers variables fuel
          parentType source rest path deferMap middle lower _ (Nat.le_trans hls hle) hmv (hm.extend he hle) hl
          (fun p hmem => groupsKnown_extend (hk p (List.mem_cons_of_mem _ hmem)) he hle)
          (fun p hmem => hp p (List.mem_cons_of_mem _ hmem))
        have hpart := hp (usages, groups) (by simp)
        have hf := deferred_workAt final lower _ deferMap usages path
          ((executeCollectedFields schema resolvers variables fuel parentType source groups path usages deferMap).run state).1.result
          _ ((hm.extend he hle).extend het hlt) hl hpart.1 hpart.2.1 (hw.extend het hlt)
        simp only [collectExecutionGroups, executeExecutionGroup, run_bind, StateT.run_pure, id_pure_eq]
        exact ⟨Nat.le_trans hle hlt, final, he.trans het hle, hfv,
          workAt_combine hf hwt⟩
  termination_by (fuel, 5, 0, sizeOf partitions)
  decreasing_by
    all_goals subst_vars; simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right
    all_goals try omega

  theorem executeCollectedFields_keys (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variables : VariableValues) (fuel : Nat) (parentType : Name)
      (source : ResolverValue ObjectRef) (groups : CollectedFieldsMap)
      (path : ResponsePath) (usages : List Nat) (deferMap : DeferMap)
      (parents : Assignment) (lower state : Nat) (hls : lower ≤ state)
      (hv : Valid parents state) (hm : MapAt parents state deferMap)
      (hl : MapLower lower deferMap)
      (hk
        : GroupsSatisfy
            (fun field => OptionalUsageAt parents state deferMap field.deferUsage) groups)
      (hu : GroupsUnder usages groups)
      : Completed parents lower state
          ((executeCollectedFields schema resolvers variables fuel parentType source
              groups path usages deferMap).run
            state) := by
    cases groups with
    | nil =>
        simpa only [executeCollectedFields_nil, StateT.run_pure, id_pure_eq, Completed,
          Completion.pure]
          using output_empty parents lower state hv
    | cons group rest =>
        rcases group with ⟨name, fields⟩
        obtain ⟨hle, middle, he, hmv, hw⟩ := executeResponseField_keys schema resolvers
          variables fuel parentType source
          name fields path usages deferMap parents lower state hls hv hm hl (hk (name, fields) (by simp))
          (hu (name, fields) (by simp))
        obtain ⟨hlt, final, het, hfv, hwt⟩ := executeCollectedFields_keys schema resolvers variables fuel
          parentType source rest path usages deferMap middle lower _ (Nat.le_trans hls hle) hmv (hm.extend he hle) hl
          (groupsKnown_extend (fun g hg => hk g (List.mem_cons_of_mem _ hg)) he hle)
          (fun g hg => hu g (List.mem_cons_of_mem _ hg))
        simp only [executeCollectedFields_cons, run_bind, StateT.run_pure, id_pure_eq]
        exact ⟨Nat.le_trans hle hlt, final, he.trans het hle, hfv,
          workAt_completionCombine final lower _ List.append _ _ (hw.extend het hlt) hwt⟩
  termination_by (fuel, 4, 0, sizeOf groups)
  decreasing_by
    all_goals subst_vars; simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right
    all_goals try omega

  theorem executeResponseField_keys (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variables : VariableValues) (fuel : Nat) (parentType : Name)
      (source : ResolverValue ObjectRef) (name : Name) (fields : List ExecutableField)
      (path : ResponsePath) (usages : List Nat) (deferMap : DeferMap)
      (parents : Assignment) (lower state : Nat) (hls : lower ≤ state)
      (hv : Valid parents state) (hm : MapAt parents state deferMap)
      (hl : MapLower lower deferMap)
      (hk : ∀ field ∈ fields, OptionalUsageAt parents state deferMap field.deferUsage)
      (hu : FieldsUnder usages fields)
      : Completed parents lower state
          ((executeResponseField schema resolvers variables fuel parentType source name
              fields path usages deferMap).run
            state) := by
    cases fuel with
    | zero =>
        simpa only [executeResponseField, StateT.run_pure, id_pure_eq, Completed,
          Completion.error]
          using output_empty parents lower state hv
    | succ fuel =>
        cases fields with
        | nil =>
            simpa only [executeResponseField, StateT.run_pure, id_pure_eq, Completed,
              Completion.error]
              using output_empty parents lower state hv
        | cons field rest =>
            simp only [executeResponseField]
            split
            · exact output_empty parents lower state hv
            · split
              · exact output_empty parents lower state hv
              · split
                · exact output_empty parents lower state hv
                · obtain ⟨hle, next, he, hnv, hw⟩ := completeValue_keys schema resolvers variables fuel _ _ _
                    (path ++ [.field name]) usages deferMap true parents lower state hls hv hm hl hk hu
                  simp only [run_bind, StateT.run_pure, id_pure_eq]
                  exact ⟨hle, next, he, hnv, workAt_map next lower _ _ _ hw⟩
  termination_by (fuel, 3, 0, sizeOf fields)
  decreasing_by
    all_goals subst_vars; simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right

  theorem completeValue_keys (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variables : VariableValues) (fuel : Nat) (fieldType : TypeRef)
      (fields : List ExecutableField) (value : ResolverValue ObjectRef)
      (path : ResponsePath) (usages : List Nat) (deferMap : DeferMap) (allowStream : Bool)
      (parents : Assignment) (lower state : Nat) (hls : lower ≤ state)
      (hv : Valid parents state) (hm : MapAt parents state deferMap)
      (hl : MapLower lower deferMap)
      (hk : ∀ field ∈ fields, OptionalUsageAt parents state deferMap field.deferUsage)
      (hu : FieldsUnder usages fields)
      : Completed parents lower state
          ((completeValue schema resolvers variables fuel fieldType fields value path
              usages deferMap allowStream).run
            state) := by
    cases fuel with
    | zero =>
        simpa only [completeValue, StateT.run_pure, id_pure_eq, Completed,
          Completion.error]
          using output_empty parents lower state hv
    | succ fuel =>
        cases fieldType with
        | nonNull inner =>
            obtain ⟨hle, next, he, hnv, hw⟩ := completeValue_keys schema resolvers variables (fuel + 1) inner fields
              value path usages deferMap allowStream parents lower state hls hv hm hl hk hu
            simp only [completeValue, run_bind, StateT.run_pure, id_pure_eq]
            exact ⟨hle, next, he, hnv, workAt_nonNull next lower _ _ hw⟩
        | named parentType =>
            cases value with
            | null =>
                simpa only [completeValue, StateT.run_pure, id_pure_eq, Completed,
                  Completion.pure]
                  using output_empty parents lower state hv
            | scalar scalar =>
                simp only [completeValue]; split <;> exact output_empty parents lower state hv
            | list items =>
                simpa only [completeValue, StateT.run_pure, id_pure_eq, Completed,
                  Completion.error]
                  using output_empty parents lower state hv
            | object runtimeType ref =>
                simp only [completeValue]
                split
                · exact output_empty parents lower state hv
                · obtain ⟨hsc, middle, he, hmv, hmap, hfields⟩ := collectSubfields_ancestry schema variables runtimeType
                    (.object runtimeType ref) fields parents state deferMap path hv hm hk
                  have hkc := collectSubfields_keys schema variables runtimeType (.object runtimeType ref) fields state
                    (fun field hf => optionalUsageAt_before hv (hk field hf))
                  have hlow := mapLower_new lower state deferMap _ path hl hls (fun u hu => (hkc.2.2 u hu).1)
                  have hn := collectSubfields_nonempty schema variables runtimeType (.object runtimeType ref) fields state
                  obtain ⟨hle, next, he', hnv, hw⟩ := executePlan_keys schema resolvers variables fuel runtimeType
                    (.object runtimeType ref) _ path usages deferMap middle lower _ (Nat.le_trans hls hsc) hmv hmap hlow hfields hn
                    (collectSubfields_under schema variables runtimeType (.object runtimeType ref) fields usages state hu)
                  simp only [run_bind, StateT.run_pure, id_pure_eq]
                  exact ⟨Nat.le_trans hsc hle, next, he.trans he' hsc, hnv, workAt_catchNull next lower _ _ _ hw⟩
        | list inner =>
            cases value with
            | null =>
                simpa only [completeValue, StateT.run_pure, id_pure_eq, Completed,
                  Completion.pure]
                  using output_empty parents lower state hv
            | scalar scalar =>
                simpa only [completeValue, StateT.run_pure, id_pure_eq, Completed,
                  Completion.error]
                  using output_empty parents lower state hv
            | object runtimeType ref =>
                simpa only [completeValue, StateT.run_pure, id_pure_eq, Completed,
                  Completion.error]
                  using output_empty parents lower state hv
            | list items =>
                simpa only [completeValue]
                  using completeListValueWithStream_keys schema resolvers variables fuel
                    inner fields items path usages deferMap allowStream parents lower
                    state hls hv hm hl hk hu
  termination_by (fuel, 1, sizeOf fieldType, 0)
  decreasing_by
    all_goals subst_vars; simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right

  theorem completeListValueWithStream_keys (schema : Schema)
      (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
      (inner : TypeRef) (fields : List ExecutableField)
      (values : List (ResolverValue ObjectRef)) (path : ResponsePath) (usages : List Nat)
      (deferMap : DeferMap) (allowStream : Bool) (parents : Assignment)
      (lower state : Nat) (hls : lower ≤ state) (hv : Valid parents state)
      (hm : MapAt parents state deferMap) (hl : MapLower lower deferMap)
      (hk : ∀ field ∈ fields, OptionalUsageAt parents state deferMap field.deferUsage)
      (hu : FieldsUnder usages fields)
      : Completed parents lower state
          ((completeListValueWithStream schema resolvers variables fuel inner fields
              values path usages deferMap allowStream).run
            state) := by
    unfold completeListValueWithStream
    dsimp only
    split
    · exact output_empty parents lower state hv
    · obtain ⟨hle, next, he, hnv, hw⟩ := completeListValue_keys schema resolvers variables
        fuel inner fields values
        path 0 usages deferMap parents lower state hls hv hm hl hk hu
      simp only [run_bind, StateT.run_pure, id_pure_eq]
      exact ⟨hle, next, he, hnv, workAt_catchNull next lower _ _ _ hw⟩
    · rename_i usage _
      obtain ⟨hle, middle, he, hmv, hw⟩ := completeListValue_keys schema resolvers
        variables fuel inner fields
        (values.take usage.initialCount) path 0 usages deferMap parents lower state hls hv hm hl hk hu
      simp only [run_bind]
      split
      · exact ⟨hle, middle, he, hmv, workAt_catchNull middle lower _ _ _ hw⟩
      · split
        · exact ⟨hle, middle, he, hmv, workAt_catchNull middle lower _ _ _ hw⟩
        · let middleState := ((completeListValue schema resolvers variables fuel inner fields
            (values.take usage.initialCount) path 0 usages deferMap).run state).2
          have hav : Valid (allocate middle middleState []) (middleState + 1) :=
            allocate_valid middle middleState none hmv (by simp)
          obtain ⟨hlt, final, het, hfv, hitems⟩ := completeStreamItems_keys schema resolvers variables fuel inner
            (fields.map (fun field => { field with deferUsage := none })) (values.drop usage.initialCount)
            path usage.initialCount (allocate middle middleState []) (middleState + 1) (middleState + 1)
            (Nat.le_refl _) hav (by intro f hf; obtain ⟨old, _, rfl⟩ := List.mem_map.mp hf; rfl)
          have hea := allocate_extends middle middleState []
          have heall := hea.trans het (Nat.le_succ middleState)
          simp only [freshExecutionKey, run_bind, StateT.run_get, StateT.run_set, StateT.run_pure, id_pure_eq]
          refine ⟨by dsimp only [middleState] at *; omega, final, he.trans heall hle, hfv, ?_⟩
          apply workAt_combine (workAt_catchNull final lower _ _ _
            (hw.extend heall (by dsimp only [middleState] at *; omega)))
          rw [WorkAt]
          exact ⟨Nat.le_trans hls hle, by dsimp only [middleState] at *; omega, hitems⟩
  termination_by (fuel, 3, 0, 0)
  decreasing_by
    all_goals subst_vars; simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right

  theorem completeListValue_keys (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variables : VariableValues) (fuel : Nat) (itemType : TypeRef)
      (fields : List ExecutableField) (values : List (ResolverValue ObjectRef))
      (path : ResponsePath) (index : Nat) (usages : List Nat) (deferMap : DeferMap)
      (parents : Assignment) (lower state : Nat) (hls : lower ≤ state)
      (hv : Valid parents state) (hm : MapAt parents state deferMap)
      (hl : MapLower lower deferMap)
      (hk : ∀ field ∈ fields, OptionalUsageAt parents state deferMap field.deferUsage)
      (hu : FieldsUnder usages fields)
      : Completed parents lower state
          ((completeListValue schema resolvers variables fuel itemType fields values path
              index usages deferMap).run
            state) := by
    cases values with
    | nil =>
        simpa only [completeListValue, StateT.run_pure, id_pure_eq, Completed,
          Completion.pure]
          using output_empty parents lower state hv
    | cons value rest =>
        obtain ⟨hle, middle, he, hmv, hw⟩ := completeValue_keys schema resolvers variables fuel itemType fields value
          (path ++ [.index index]) usages deferMap false parents lower state hls hv hm hl hk hu
        obtain ⟨hlt, final, het, hfv, hwt⟩ := completeListValue_keys schema resolvers
          variables fuel itemType fields rest
          path (index + 1) usages deferMap middle lower _ (Nat.le_trans hls hle) hmv (hm.extend he hle) hl
          (fieldsKnown_extend hk he hle) hu
        simp only [completeListValue, run_bind, StateT.run_pure, id_pure_eq]
        exact ⟨Nat.le_trans hle hlt, final, he.trans het hle, hfv,
          workAt_completionCombine final lower _ List.cons _ _ (hw.extend het hlt) hwt⟩
  termination_by (fuel, 2, sizeOf itemType, sizeOf values)
  decreasing_by
    all_goals subst_vars; simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right
    all_goals try omega

  theorem completeStreamItems_keys (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variables : VariableValues) (fuel : Nat) (itemType : TypeRef)
      (fields : List ExecutableField) (values : List (ResolverValue ObjectRef))
      (path : ResponsePath) (index : Nat) (parents : Assignment) (lower state : Nat)
      (hls : lower ≤ state) (hv : Valid parents state)
      (hk : ∀ field ∈ fields, field.deferUsage = none)
      : let output :=
          (completeStreamItems schema resolvers variables fuel itemType fields values path
            index).run
            state
        state ≤ output.2
        ∧ ∃ next,
            Extends state parents next
            ∧ Valid next output.2
            ∧ ∀ item ∈ output.1, WorkAt next lower output.2 item.2 := by
    cases values with
    | nil =>
        simp only [completeStreamItems, StateT.run_pure, id_pure_eq]
        exact ⟨Nat.le_refl _, parents, Extends.refl _ _, hv, by simp⟩
    | cons value rest =>
        obtain ⟨hle, middle, he, hmv, hw⟩ := completeValue_keys schema resolvers variables fuel itemType fields value
          (path ++ [.index index]) [] [] false parents lower state hls hv
          (by simp [MapAt]) (by simp [MapLower, mapKeys]) (by intro f hf; simp [OptionalUsageAt, hk f hf])
          (fun _ _ => Or.inl rfl)
        simp only [completeStreamItems, run_bind]
        split
        · exact ⟨hle, middle, he, hmv, by simp [WorkAt]⟩
        · obtain ⟨hlt, final, het, hfv, htail⟩ := completeStreamItems_keys schema resolvers variables fuel itemType fields rest
            path (index + 1) middle lower _ (Nat.le_trans hls hle) hmv hk
          simp only [run_bind, StateT.run_pure, id_pure_eq]
          refine ⟨Nat.le_trans hle hlt, final, he.trans het hle, hfv, ?_⟩
          intro item hi
          rcases List.mem_cons.mp hi with rfl | hi
          · exact hw.extend het hlt
          · exact htail item hi
  termination_by (fuel, 2, sizeOf itemType, sizeOf values)
  decreasing_by
    all_goals subst_vars; simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right
    all_goals try omega
end

theorem executeRoot_keys (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues) (fuel : Nat) (parentType : Name)
    (source : ResolverValue ObjectRef) (selections : List Selection) (state : Nat)
    : let output :=
        (executeRootSelectionSetCore schema resolvers variables fuel parentType source
          selections).run
          state
      state ≤ output.2
      ∧ ∃ parents,
          Valid parents output.2 ∧ WorkAt parents state output.2 output.1.work := by
  obtain ⟨hsc, middle, _, hmv, hm, hk⟩ := collectFields_ancestry schema variables parentType source selections none
    (fun _ => []) state [] [] (by simp [Valid]) (by simp [MapAt]) (by simp [OptionalUsageAt])
  have hkc := collectFields_keys schema variables parentType source selections none state (by simp [UsageBefore])
  have hl := mapLower_new state state [] _ [] (by simp [MapLower, mapKeys]) (Nat.le_refl _)
    (fun u hu => (hkc.2.2 u hu).1)
  obtain ⟨hle, parents, _, hv, hw⟩ := executePlan_keys schema resolvers variables fuel parentType source
    _ [] [] [] middle state _ hsc hmv hm hl hk
    (collectFields_nonempty schema variables parentType source selections none state)
    (fun _ _ _ _ => Or.inl rfl)
  exact ⟨Nat.le_trans hsc hle, parents, hv, hw⟩

theorem executeRoot_taskKey_bounds (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues) (fuel : Nat) (parentType : Name)
    (source : ResolverValue ObjectRef) (selections : List Selection) (state key : Nat)
    (hk
      : TaskKey key
          ((executeRootSelectionSetCore schema resolvers variables fuel parentType source
              selections).run
            state).1.work)
    : state ≤ key
      ∧ key
        < ((executeRootSelectionSetCore schema resolvers variables fuel parentType source
              selections).run
            state).2 := by
  obtain ⟨_, _, _, hw⟩ := executeRoot_keys schema resolvers variables fuel parentType source selections state
  exact hw.key_bounds hk

end GraphQL.IncrementalDelivery.Semantics.MixedKeys
