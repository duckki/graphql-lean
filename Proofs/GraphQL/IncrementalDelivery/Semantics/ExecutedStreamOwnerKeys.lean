import Proofs.GraphQL.IncrementalDelivery.Semantics.StreamOwnerKeys

/-! Actual execution allocates stream nodes after their deferred owners.
Stream keys are bounded below by the execution state before completion, while
every deferred fragment looked up for that completion has an earlier key.
-/

namespace GraphQL.IncrementalDelivery.Semantics.GeneralScheduling

open GraphQL.IncrementalDelivery.Execution

attribute [local simp] id_pure_eq id_bind_eq id_map_eq run_bind run_map

mutual
  theorem executePlan_streamOwnerKeys (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variables : VariableValues) (fuel : Nat) (parentType : Name)
      (source : ResolverValue ObjectRef) (collection : FieldCollection)
      (path : ResponsePath) (usages : List Nat) (deferMap : DeferMap) (state : Nat)
      (hm : DeferMapBefore state (getNewDeferMap collection.newDeferUsages path deferMap))
      (hk
        : GroupsSatisfy (fun field => UsageBefore state field.deferUsage)
            collection.fields)
      : StreamKeyCompleted state
          ((executeExecutionPlan schema resolvers variables fuel parentType source
              collection.newDeferUsages (buildExecutionPlan collection.fields usages) path
              usages deferMap).run
            state) := by
    have hp := buildExecutionPlan_preserves_property _ collection.fields usages hk
    obtain ⟨hle, hw, ho⟩ := executeCollectedFields_streamOwnerKeys schema resolvers variables fuel parentType source
      _ path usages _ state hm hp.1
    simp only [executeExecutionPlan, run_bind]
    split
    · exact ⟨hle, hw, ho⟩
    · obtain ⟨hlt, hwt, hot⟩ := collectExecutionGroups_streamOwnerKeys schema resolvers variables fuel parentType source
        _ path _ _ (hm.mono hle) (fun p hmem g hg f hf => usageBefore_mono _ (hp.2 p hmem g hg f hf) hle)
      simp only [run_bind, StateT.run_pure, id_pure_eq]
      exact ⟨Nat.le_trans hle hlt, streamKeys_append ⟨hw, ho⟩ ⟨hwt.mono hle, hot⟩⟩
  termination_by (fuel, 6, 0, 0)
  decreasing_by
    all_goals simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right

  theorem collectExecutionGroups_streamOwnerKeys (schema : Schema)
      (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
      (parentType : Name) (source : ResolverValue ObjectRef)
      (partitions : List (List Nat × CollectedFieldsMap)) (path : ResponsePath)
      (deferMap : DeferMap) (state : Nat) (hm : DeferMapBefore state deferMap)
      (hk
        : ∀ partition ∈ partitions,
            GroupsSatisfy (fun field => UsageBefore state field.deferUsage) partition.2)
      : StreamKeyOutput state
          ((collectExecutionGroups schema resolvers variables fuel parentType source
              partitions path deferMap).run
            state).1
          ((collectExecutionGroups schema resolvers variables fuel parentType source
              partitions path deferMap).run
            state).2 := by
    cases partitions with
    | nil =>
        simpa only [collectExecutionGroups, StateT.run_pure, id_pure_eq] using streamKeyOutput_empty state
    | cons partition rest =>
        rcases partition with ⟨usages, groups⟩
        obtain ⟨hle, hw, ho⟩ := executeCollectedFields_streamOwnerKeys schema resolvers variables fuel parentType source
          groups path usages deferMap state hm (hk (usages, groups) (by simp))
        obtain ⟨hlt, hwt, hot⟩ := collectExecutionGroups_streamOwnerKeys schema resolvers variables fuel parentType source
          rest path deferMap _ (hm.mono hle)
          (fun p hmem g hg f hf => usageBefore_mono _ (hk p (List.mem_cons_of_mem _ hmem) g hg f hf) hle)
        have hd := streamKeys_deferred state deferMap usages path
          ((executeCollectedFields schema resolvers variables fuel parentType source groups path usages deferMap).run state).1.result
          _ hm ⟨hw, ho⟩
        simp only [collectExecutionGroups, executeExecutionGroup, run_bind, StateT.run_pure, id_pure_eq]
        exact ⟨Nat.le_trans hle hlt, streamKeys_append hd ⟨hwt.mono hle, hot⟩⟩
  termination_by (fuel, 5, 0, sizeOf partitions)
  decreasing_by
    all_goals subst_vars; simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right
    all_goals omega

  theorem executeCollectedFields_streamOwnerKeys (schema : Schema)
      (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
      (parentType : Name) (source : ResolverValue ObjectRef) (groups : CollectedFieldsMap)
      (path : ResponsePath) (usages : List Nat) (deferMap : DeferMap) (state : Nat)
      (hm : DeferMapBefore state deferMap)
      (hk : GroupsSatisfy (fun field => UsageBefore state field.deferUsage) groups)
      : StreamKeyCompleted state
          ((executeCollectedFields schema resolvers variables fuel parentType source
              groups path usages deferMap).run
            state) := by
    cases groups with
    | nil =>
        simpa only [executeCollectedFields_nil, StateT.run_pure, id_pure_eq,
          StreamKeyCompleted, Completion.pure]
          using streamKeyOutput_empty state
    | cons group rest =>
        rcases group with ⟨name, fields⟩
        obtain ⟨hle, hw, ho⟩ := executeResponseField_streamOwnerKeys schema resolvers
          variables fuel parentType source
          name fields path usages deferMap state hm (hk (name, fields) (by simp))
        obtain ⟨hlt, hwt, hot⟩ := executeCollectedFields_streamOwnerKeys schema resolvers variables fuel parentType source
          rest path usages deferMap _ (hm.mono hle)
          (fun g hg f hf => usageBefore_mono _ (hk g (List.mem_cons_of_mem _ hg) f hf) hle)
        simp only [executeCollectedFields_cons, run_bind, StateT.run_pure, id_pure_eq]
        exact ⟨
          Nat.le_trans hle hlt,
          streamKeys_combine state List.append _ _ ⟨hw, ho⟩ ⟨hwt.mono hle, hot⟩
        ⟩
  termination_by (fuel, 4, 0, sizeOf groups)
  decreasing_by
    all_goals subst_vars; simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right
    all_goals omega

  theorem executeResponseField_streamOwnerKeys (schema : Schema)
      (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
      (parentType : Name) (source : ResolverValue ObjectRef) (name : Name)
      (fields : List ExecutableField) (path : ResponsePath) (usages : List Nat)
      (deferMap : DeferMap) (state : Nat) (hm : DeferMapBefore state deferMap)
      (hk : ∀ field ∈ fields, UsageBefore state field.deferUsage)
      : StreamKeyCompleted state
          ((executeResponseField schema resolvers variables fuel parentType source name
              fields path usages deferMap).run
            state) := by
    cases fuel with
    | zero =>
        simpa only [executeResponseField, StateT.run_pure, id_pure_eq, StreamKeyCompleted,
          Completion.error]
          using streamKeyOutput_empty state
    | succ fuel =>
        cases fields with
        | nil =>
            simpa only [executeResponseField, StateT.run_pure, id_pure_eq,
              StreamKeyCompleted, Completion.error]
              using streamKeyOutput_empty state
        | cons field rest =>
            simp only [executeResponseField]
            split
            · exact streamKeyOutput_empty state
            · split
              · exact streamKeyOutput_empty state
              · split
                · exact streamKeyOutput_empty state
                · obtain ⟨hle, hw, ho⟩ := completeValue_streamOwnerKeys schema resolvers variables fuel _ _ _
                    (path ++ [.field name]) usages deferMap true state hm hk
                  simp only [run_bind, StateT.run_pure, id_pure_eq]
                  exact ⟨hle, streamKeys_map state _ _ ⟨hw, ho⟩⟩
  termination_by (fuel, 3, 0, sizeOf fields)
  decreasing_by
    all_goals subst_vars; simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right

  theorem completeValue_streamOwnerKeys (schema : Schema)
      (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
      (fieldType : TypeRef) (fields : List ExecutableField)
      (value : ResolverValue ObjectRef) (path : ResponsePath) (usages : List Nat)
      (deferMap : DeferMap) (allowStream : Bool) (state : Nat)
      (hm : DeferMapBefore state deferMap)
      (hk : ∀ field ∈ fields, UsageBefore state field.deferUsage)
      : StreamKeyCompleted state
          ((completeValue schema resolvers variables fuel fieldType fields value path
              usages deferMap allowStream).run
            state) := by
    cases fuel with
    | zero =>
        simpa only [completeValue, StateT.run_pure, id_pure_eq, StreamKeyCompleted,
          Completion.error]
          using streamKeyOutput_empty state
    | succ fuel =>
        cases fieldType with
        | nonNull inner =>
            obtain ⟨hle, hw, ho⟩ := completeValue_streamOwnerKeys schema resolvers variables (fuel + 1) inner fields
              value path usages deferMap allowStream state hm hk
            simp only [completeValue, run_bind, StateT.run_pure, id_pure_eq]
            exact ⟨hle, streamKeys_nonNull state _ ⟨hw, ho⟩⟩
        | named parentType =>
            cases value with
            | null =>
                simpa only [completeValue, StateT.run_pure, id_pure_eq,
                  StreamKeyCompleted, Completion.pure]
                  using streamKeyOutput_empty state
            | scalar scalar =>
                simp only [completeValue]; split <;> exact streamKeyOutput_empty state
            | list items =>
                simpa only [completeValue, StateT.run_pure, id_pure_eq,
                  StreamKeyCompleted, Completion.error]
                  using streamKeyOutput_empty state
            | object runtimeType ref =>
                simp only [completeValue]
                split
                · exact streamKeyOutput_empty state
                · have hc := collectSubfields_keys schema variables runtimeType (.object runtimeType ref) fields state hk
                  have hm' := deferMapBefore_new hm hc.1 _ (fun u hu => (hc.2.2 u hu).2.1) path
                  obtain ⟨hle, hw, ho⟩ := executePlan_streamOwnerKeys schema resolvers variables fuel runtimeType
                    (.object runtimeType ref) _ path usages deferMap _ hm' hc.2.1
                  simp only [run_bind, StateT.run_pure, id_pure_eq]
                  exact ⟨Nat.le_trans hc.1 hle, streamKeys_catchNull state _ _ ⟨hw.mono hc.1, ho⟩⟩
        | list inner =>
            cases value with
            | null =>
                simpa only [completeValue, StateT.run_pure, id_pure_eq,
                  StreamKeyCompleted, Completion.pure]
                  using streamKeyOutput_empty state
            | scalar scalar =>
                simpa only [completeValue, StateT.run_pure, id_pure_eq,
                  StreamKeyCompleted, Completion.error]
                  using streamKeyOutput_empty state
            | object runtimeType ref =>
                simpa only [completeValue, StateT.run_pure, id_pure_eq,
                  StreamKeyCompleted, Completion.error]
                  using streamKeyOutput_empty state
            | list items =>
                simpa only [completeValue]
                  using completeListValueWithStream_streamOwnerKeys schema resolvers
                    variables fuel inner fields items path usages deferMap allowStream
                    state hm hk
  termination_by (fuel, 1, sizeOf fieldType, 0)
  decreasing_by
    all_goals subst_vars; simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right

  theorem completeListValueWithStream_streamOwnerKeys (schema : Schema)
      (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
      (inner : TypeRef) (fields : List ExecutableField)
      (values : List (ResolverValue ObjectRef)) (path : ResponsePath) (usages : List Nat)
      (deferMap : DeferMap) (allowStream : Bool) (state : Nat)
      (hm : DeferMapBefore state deferMap)
      (hk : ∀ field ∈ fields, UsageBefore state field.deferUsage)
      : StreamKeyCompleted state
          ((completeListValueWithStream schema resolvers variables fuel inner fields
              values path usages deferMap allowStream).run
            state) := by
    unfold completeListValueWithStream
    dsimp only
    split
    · exact streamKeyOutput_empty state
    · obtain ⟨hle, hw, ho⟩ := completeListValue_streamOwnerKeys schema resolvers variables
        fuel inner fields values
        path 0 usages deferMap state hm hk
      simp only [run_bind, StateT.run_pure, id_pure_eq]
      exact ⟨hle, streamKeys_catchNull state _ _ ⟨hw, ho⟩⟩
    · rename_i usage _
      obtain ⟨hle, hw, ho⟩ := completeListValue_streamOwnerKeys schema resolvers variables
        fuel inner fields
        (values.take usage.initialCount) path 0 usages deferMap state hm hk
      simp only [run_bind]
      split
      · exact ⟨hle, streamKeys_catchNull state _ _ ⟨hw, ho⟩⟩
      · split
        · exact ⟨hle, streamKeys_catchNull state _ _ ⟨hw, ho⟩⟩
        · let middle := ((completeListValue schema resolvers variables fuel inner fields
            (values.take usage.initialCount) path 0 usages deferMap).run state).2
          obtain ⟨hlt, hitems⟩ := completeStreamItems_streamOwnerKeys schema resolvers variables fuel inner
            (fields.map (fun field => { field with deferUsage := none })) (values.drop usage.initialCount)
            path usage.initialCount (middle + 1)
            (by intro f hf; obtain ⟨old, _, rfl⟩ := List.mem_map.mp hf; simp [UsageBefore])
          simp only [freshExecutionKey, run_bind, StateT.run_get, StateT.run_set, StateT.run_pure, id_pure_eq]
          refine ⟨by dsimp only [middle] at *; omega, ?_⟩
          apply streamKeys_append (streamKeys_catchNull state _ _ ⟨hw, ho⟩)
          simp only [StreamKeysFrom, StreamOwnersOrdered]
          exact ⟨⟨hle, fun item hi => (hitems item hi).1.mono (by dsimp only [middle]; omega)⟩,
            fun item hi => (hitems item hi).2⟩
  termination_by (fuel, 3, 0, 0)
  decreasing_by
    all_goals subst_vars; simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right

  theorem completeListValue_streamOwnerKeys (schema : Schema)
      (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
      (itemType : TypeRef) (fields : List ExecutableField)
      (values : List (ResolverValue ObjectRef)) (path : ResponsePath) (index : Nat)
      (usages : List Nat) (deferMap : DeferMap) (state : Nat)
      (hm : DeferMapBefore state deferMap)
      (hk : ∀ field ∈ fields, UsageBefore state field.deferUsage)
      : StreamKeyCompleted state
          ((completeListValue schema resolvers variables fuel itemType fields values path
              index usages deferMap).run
            state) := by
    cases values with
    | nil =>
        simpa only [completeListValue, StateT.run_pure, id_pure_eq, StreamKeyCompleted,
          Completion.pure]
          using streamKeyOutput_empty state
    | cons value rest =>
        obtain ⟨hle, hw, ho⟩ := completeValue_streamOwnerKeys schema resolvers variables fuel itemType fields value
          (path ++ [.index index]) usages deferMap false state hm hk
        obtain ⟨hlt, hwt, hot⟩ := completeListValue_streamOwnerKeys schema resolvers
          variables fuel itemType fields rest
          path (index + 1) usages deferMap _ (hm.mono hle) (fun f hf => usageBefore_mono _ (hk f hf) hle)
        simp only [completeListValue, run_bind, StateT.run_pure, id_pure_eq]
        exact ⟨Nat.le_trans hle hlt, streamKeys_combine state List.cons _ _ ⟨hw, ho⟩ ⟨hwt.mono hle, hot⟩⟩
  termination_by (fuel, 2, sizeOf itemType, sizeOf values)
  decreasing_by
    all_goals subst_vars; simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right
    all_goals omega

  theorem completeStreamItems_streamOwnerKeys (schema : Schema)
      (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
      (itemType : TypeRef) (fields : List ExecutableField)
      (values : List (ResolverValue ObjectRef)) (path : ResponsePath) (index : Nat)
      (state : Nat) (hk : ∀ field ∈ fields, UsageBefore state field.deferUsage)
      : let output :=
          (completeStreamItems schema resolvers variables fuel itemType fields values path
            index).run
            state
        state ≤ output.2
        ∧ ∀ item ∈ output.1,
            StreamKeysFrom state item.2 ∧ StreamOwnersOrdered item.2 := by
    cases values with
    | nil =>
        simp only [completeStreamItems, StateT.run_pure, id_pure_eq]
        exact ⟨Nat.le_refl _, by simp⟩
    | cons value rest =>
        obtain ⟨hle, hw, ho⟩ := completeValue_streamOwnerKeys schema resolvers variables fuel itemType fields value
          (path ++ [.index index]) [] [] false state (by simp [DeferMapBefore]) hk
        simp only [completeStreamItems, run_bind]
        split
        · exact ⟨hle, by simp [StreamKeysFrom, StreamOwnersOrdered]⟩
        · obtain ⟨hlt, htail⟩ := completeStreamItems_streamOwnerKeys schema resolvers variables fuel itemType fields rest
            path (index + 1) _ (fun f hf => usageBefore_mono _ (hk f hf) hle)
          simp only [run_bind, StateT.run_pure, id_pure_eq]
          refine ⟨Nat.le_trans hle hlt, ?_⟩
          intro item hi
          rcases List.mem_cons.mp hi with rfl | hi
          · exact ⟨hw, ho⟩
          · exact ⟨(htail item hi).1.mono hle, (htail item hi).2⟩
  termination_by (fuel, 2, sizeOf itemType, sizeOf values)
  decreasing_by
    all_goals subst_vars; simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right
    all_goals omega
end

theorem executeRoot_streamOwnerKeys (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues) (fuel : Nat) (parentType : Name)
    (source : ResolverValue ObjectRef) (selections : List Selection) (state : Nat)
    : StreamKeyCompleted state
        ((executeRootSelectionSetCore schema resolvers variables fuel parentType source
            selections).run
          state) := by
  have hc := collectFields_keys schema variables parentType source selections none state (by simp [UsageBefore])
  have hm := deferMapBefore_new (deferMap := []) (by simp [DeferMapBefore]) hc.1 _
    (fun u hu => (hc.2.2 u hu).2.1) []
  obtain ⟨hle, hw, ho⟩ := executePlan_streamOwnerKeys schema resolvers variables fuel parentType source
    _ [] [] [] _ hm hc.2.1
  exact ⟨Nat.le_trans hc.1 hle, hw.mono hc.1, ho⟩

theorem executeRoot_streamOwnersOrdered (schema : Schema)
    (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
    (parentType : Name) (source : ResolverValue ObjectRef) (selections : List Selection)
    (state : Nat)
    : StreamOwnersOrdered
        ((executeRootSelectionSetCore schema resolvers variables fuel parentType source
            selections).run
          state).1.work :=
  (executeRoot_streamOwnerKeys schema resolvers variables fuel parentType source
    selections state).2.2

end GraphQL.IncrementalDelivery.Semantics.GeneralScheduling
