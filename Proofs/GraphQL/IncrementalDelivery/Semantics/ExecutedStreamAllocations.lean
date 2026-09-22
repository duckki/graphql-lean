import Proofs.GraphQL.IncrementalDelivery.Semantics.StreamAllocations

/-! Every actual stream node has its own fresh allocation, even across sibling
fields and items. Inherited defer maps/usages may be arbitrary: this theorem counts
stream-node occurrences only, not deferred metadata or repeated cursor pulls.
-/

namespace GraphQL.IncrementalDelivery.Semantics.GeneralScheduling

open GraphQL.IncrementalDelivery.Execution

attribute [local simp] id_pure_eq id_bind_eq id_map_eq run_bind run_map

mutual
  theorem executePlan_streamAllocations (schema : Schema)
      (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
      (parentType : Name) (source : ResolverValue ObjectRef)
      (collection : FieldCollection) (path : ResponsePath) (usages : List Nat)
      (deferMap : DeferMap) (state : Nat)
      : StreamsCompleted state
          ((executeExecutionPlan schema resolvers variables fuel parentType source
              collection.newDeferUsages (buildExecutionPlan collection.fields usages) path
              usages deferMap).run
            state) := by
    have hl := executeCollectedFields_streamAllocations schema resolvers variables fuel
      parentType source (buildExecutionPlan collection.fields usages).collectedFieldsMap
      path usages (getNewDeferMap collection.newDeferUsages path deferMap) state
    simp only [executeExecutionPlan, run_bind]
    split
    · exact hl
    · simp only [run_bind, StateT.run_pure, id_pure_eq]
      exact streams_combine hl (collectExecutionGroups_streamAllocations schema resolvers variables fuel
        parentType source _ path _ _)
  termination_by (fuel, 6, 0, 0)
  decreasing_by
    all_goals simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right

  theorem collectExecutionGroups_streamAllocations (schema : Schema)
      (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
      (parentType : Name) (source : ResolverValue ObjectRef)
      (partitions : List (List Nat × CollectedFieldsMap)) (path : ResponsePath)
      (deferMap : DeferMap) (state : Nat)
      : let output :=
          (collectExecutionGroups schema resolvers variables fuel parentType
            source partitions path deferMap).run
            state
        StreamAllocated state output.1 output.2 := by
    cases partitions with
    | nil =>
        simpa only [collectExecutionGroups, StateT.run_pure, id_pure_eq] using streams_empty state
    | cons partition rest =>
        rcases partition with ⟨usages, groups⟩
        have hl := executeCollectedFields_streamAllocations schema resolvers variables fuel
          parentType source groups path usages deferMap state
        have hr := collectExecutionGroups_streamAllocations schema resolvers variables fuel
          parentType source rest path deferMap
          ((executeCollectedFields schema resolvers variables fuel parentType source groups path usages deferMap).run state).2
        simp only [collectExecutionGroups, executeExecutionGroup, run_bind, StateT.run_pure, id_pure_eq]
        apply streams_combine
        · simpa only [StreamsCompleted, StreamAllocated, streamAllocationKeys] using hl
        · exact hr
  termination_by (fuel, 5, 0, sizeOf partitions)
  decreasing_by
    all_goals subst_vars; simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right
    all_goals omega

  theorem executeCollectedFields_streamAllocations (schema : Schema)
      (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
      (parentType : Name) (source : ResolverValue ObjectRef) (groups : CollectedFieldsMap)
      (path : ResponsePath) (usages : List Nat) (deferMap : DeferMap) (state : Nat)
      : StreamsCompleted state
          ((executeCollectedFields schema resolvers variables fuel parentType source
              groups path usages deferMap).run
            state) := by
    cases groups with
    | nil =>
        simpa only [executeCollectedFields_nil, StateT.run_pure, id_pure_eq,
          StreamsCompleted, Completion.pure]
          using streams_empty state
    | cons group rest =>
        rcases group with ⟨name, fields⟩
        have hl := executeResponseField_streamAllocations schema resolvers variables fuel parentType
          source name fields path usages deferMap state
        have hr := executeCollectedFields_streamAllocations schema resolvers variables fuel
          parentType source rest path usages deferMap
          ((executeResponseField schema resolvers variables fuel parentType source name
            fields path usages deferMap).run state).2
        simp only [executeCollectedFields_cons, run_bind, StateT.run_pure, id_pure_eq]
        exact streams_completionCombine List.append _ _ hl hr
  termination_by (fuel, 4, 0, sizeOf groups)
  decreasing_by
    all_goals subst_vars; simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right
    all_goals omega

  theorem executeResponseField_streamAllocations (schema : Schema)
      (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
      (parentType : Name) (source : ResolverValue ObjectRef) (name : Name)
      (fields : List ExecutableField) (path : ResponsePath) (usages : List Nat)
      (deferMap : DeferMap) (state : Nat)
      : StreamsCompleted state
          ((executeResponseField schema resolvers variables fuel parentType source name
              fields path usages deferMap).run
            state) := by
    cases fuel with
    | zero =>
        simpa only [executeResponseField, StateT.run_pure, id_pure_eq, StreamsCompleted,
          Completion.error]
          using streams_empty state
    | succ fuel =>
        cases fields with
        | nil =>
            simpa only [executeResponseField, StateT.run_pure, id_pure_eq,
              StreamsCompleted, Completion.error]
              using streams_empty state
        | cons field rest =>
            simp only [executeResponseField]
            split
            · exact streams_empty state
            · split
              · exact streams_empty state
              · split
                · exact streams_empty state
                · simp only [run_bind, StateT.run_pure, id_pure_eq]
                  apply streams_map
                  exact completeValue_streamAllocations schema resolvers variables fuel _ _ _
                    (path ++ [.field name]) usages deferMap true state
  termination_by (fuel, 3, 0, sizeOf fields)
  decreasing_by
    all_goals subst_vars; simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right

  theorem completeValue_streamAllocations (schema : Schema)
      (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
      (fieldType : TypeRef) (fields : List ExecutableField)
      (value : ResolverValue ObjectRef) (path : ResponsePath) (usages : List Nat)
      (deferMap : DeferMap) (allowStream : Bool) (state : Nat)
      : StreamsCompleted state
          ((completeValue schema resolvers variables fuel fieldType fields value path
              usages deferMap allowStream).run
            state) := by
    cases fuel with
    | zero =>
        simpa only [completeValue, StateT.run_pure, id_pure_eq, StreamsCompleted,
          Completion.error]
          using streams_empty state
    | succ fuel =>
        cases fieldType with
        | nonNull inner =>
            have h := completeValue_streamAllocations schema resolvers variables (fuel + 1)
              inner fields value path usages deferMap allowStream state
            simp only [completeValue, run_bind, StateT.run_pure, id_pure_eq]
            exact streams_nonNull _ h
        | named parentType =>
            cases value with
            | null =>
                simpa only [completeValue, StateT.run_pure, id_pure_eq, StreamsCompleted,
                  Completion.pure]
                  using streams_empty state
            | scalar scalar =>
                simp only [completeValue]; split <;> exact streams_empty state
            | list items =>
                simpa only [completeValue, StateT.run_pure, id_pure_eq, StreamsCompleted,
                  Completion.error]
                  using streams_empty state
            | object runtimeType ref =>
                simp only [completeValue]
                split
                · exact streams_empty state
                · have hc := OwnerPaths.collectSubfields_supply schema variables runtimeType
                    (.object runtimeType ref) fields state
                  have h := executePlan_streamAllocations schema resolvers variables fuel runtimeType
                    (.object runtimeType ref)
                    ((collectSubfields schema variables runtimeType (.object runtimeType ref) fields).run state).1
                    path usages deferMap
                    ((collectSubfields schema variables runtimeType (.object runtimeType ref) fields).run state).2
                  simp only [run_bind, StateT.run_pure, id_pure_eq]
                  exact streams_catchNull _ _ (h.widen hc.1 (Nat.le_refl _))
        | list inner =>
            cases value with
            | null =>
                simpa only [completeValue, StateT.run_pure, id_pure_eq, StreamsCompleted,
                  Completion.pure]
                  using streams_empty state
            | scalar scalar =>
                simpa only [completeValue, StateT.run_pure, id_pure_eq, StreamsCompleted,
                  Completion.error]
                  using streams_empty state
            | object runtimeType ref =>
                simpa only [completeValue, StateT.run_pure, id_pure_eq, StreamsCompleted,
                  Completion.error]
                  using streams_empty state
            | list items =>
                simpa only [completeValue]
                  using completeListValueWithStream_streamAllocations schema resolvers
                    variables fuel inner fields items path usages deferMap allowStream
                    state
  termination_by (fuel, 1, sizeOf fieldType, 0)
  decreasing_by
    all_goals subst_vars; simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right

  theorem completeListValueWithStream_streamAllocations (schema : Schema)
      (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
      (inner : TypeRef) (fields : List ExecutableField)
      (values : List (ResolverValue ObjectRef)) (path : ResponsePath) (usages : List Nat)
      (deferMap : DeferMap) (allowStream : Bool) (state : Nat)
      : StreamsCompleted state
          ((completeListValueWithStream schema resolvers variables fuel inner fields
              values path usages deferMap allowStream).run
            state) := by
    unfold completeListValueWithStream
    dsimp only
    split
    · exact streams_empty state
    · have h := completeListValue_streamAllocations schema resolvers variables fuel inner
        fields values path 0 usages deferMap state
      simp only [run_bind, StateT.run_pure, id_pure_eq]
      exact streams_catchNull _ _ h
    · rename_i usage _
      have hl := completeListValue_streamAllocations schema resolvers variables fuel inner
        fields (values.take usage.initialCount) path 0 usages deferMap state
      simp only [run_bind]
      split
      · exact streams_catchNull _ _ hl
      · split
        · exact streams_catchNull _ _ hl
        · let middle := ((completeListValue schema resolvers variables fuel inner fields
            (values.take usage.initialCount) path 0 usages deferMap).run state).2
          have hr := completeStreamItems_streamAllocations schema resolvers variables fuel inner
            (fields.map (fun field => {field with deferUsage := none}))
            (values.drop usage.initialCount) path usage.initialCount (middle + 1)
          simp only [freshExecutionKey, run_bind, StateT.run_get, StateT.run_set, StateT.run_pure, id_pure_eq]
          apply streams_combine (streams_catchNull _ _ hl)
          simpa only [StreamAllocated, streamAllocationKeys, itemAllocationKeys] using hr.fresh
  termination_by (fuel, 3, 0, 0)
  decreasing_by
    all_goals subst_vars; simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right

  theorem completeListValue_streamAllocations (schema : Schema)
      (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
      (itemType : TypeRef) (fields : List ExecutableField)
      (values : List (ResolverValue ObjectRef)) (path : ResponsePath) (index : Nat)
      (usages : List Nat) (deferMap : DeferMap) (state : Nat)
      : StreamsCompleted state
          ((completeListValue schema resolvers variables fuel itemType fields values path
              index usages deferMap).run
            state) := by
    cases values with
    | nil =>
        simpa only [completeListValue, StateT.run_pure, id_pure_eq, StreamsCompleted,
          Completion.pure]
          using streams_empty state
    | cons value rest =>
        have hl := completeValue_streamAllocations schema resolvers variables fuel itemType
          fields value (path ++ [.index index]) usages deferMap false state
        have hr := completeListValue_streamAllocations schema resolvers variables fuel itemType
          fields rest path (index + 1) usages deferMap
          ((completeValue schema resolvers variables fuel itemType fields value
            (path ++ [.index index]) usages deferMap false).run state).2
        simp only [completeListValue, run_bind, StateT.run_pure, id_pure_eq]
        exact streams_completionCombine List.cons _ _ hl hr
  termination_by (fuel, 2, sizeOf itemType, sizeOf values)
  decreasing_by
    all_goals subst_vars; simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right
    all_goals omega

  theorem completeStreamItems_streamAllocations (schema : Schema)
      (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
      (itemType : TypeRef) (fields : List ExecutableField)
      (values : List (ResolverValue ObjectRef)) (path : ResponsePath) (index state : Nat)
      : let output :=
          (completeStreamItems schema resolvers variables fuel itemType fields
            values path index).run
            state
        KeysAllocated state (itemAllocationKeys output.1) output.2 := by
    cases values with
    | nil =>
        simpa only [completeStreamItems, StateT.run_pure, id_pure_eq, itemAllocationKeys,
          List.flatMap_nil] using KeysAllocated.empty (Nat.le_refl state)
    | cons value rest =>
        have hl := completeValue_streamAllocations schema resolvers variables fuel itemType
          fields value (path ++ [.index index]) [] [] false state
        simp only [completeStreamItems, run_bind]
        split
        · simpa only [StateT.run_pure, id_pure_eq, itemAllocationKeys, List.flatMap_cons, List.flatMap_nil, streamAllocationKeys,
            List.append_nil] using KeysAllocated.empty hl.monotone
        · have hr := completeStreamItems_streamAllocations schema resolvers variables fuel
            itemType fields rest path (index + 1)
            ((completeValue schema resolvers variables fuel itemType fields value
              (path ++ [.index index]) [] [] false).run state).2
          simp only [run_bind, StateT.run_pure, id_pure_eq, itemAllocationKeys, List.flatMap_cons]
          exact hl.append hr
  termination_by (fuel, 2, sizeOf itemType, sizeOf values)
  decreasing_by
    all_goals subst_vars; simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right
    all_goals omega
end

theorem executeRoot_streamAllocations (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues) (fuel : Nat) (parentType : Name)
    (source : ResolverValue ObjectRef) (selections : List Selection) (state : Nat)
    : StreamsCompleted state
        ((executeRootSelectionSetCore schema resolvers variables fuel parentType source
            selections).run
          state) := by
  have hc := OwnerPaths.collectFields_supply schema variables parentType source selections none state
  let collected := (collectFields schema variables parentType source selections none).run state
  have h := executePlan_streamAllocations schema resolvers variables fuel parentType source
    collected.1 [] [] [] collected.2
  exact h.widen hc.1 (Nat.le_refl _)

theorem executeRoot_streamKeys_unique (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues) (fuel : Nat) (parentType : Name)
    (source : ResolverValue ObjectRef) (selections : List Selection) (state : Nat)
    : (streamAllocationKeys
        ((executeRootSelectionSetCore schema resolvers variables fuel parentType source
            selections).run
          state).1.work).Nodup :=
  (executeRoot_streamAllocations schema resolvers variables fuel parentType source
    selections state).unique

end GraphQL.IncrementalDelivery.Semantics.GeneralScheduling
