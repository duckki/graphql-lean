import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.DescriptorMetadata

/-! Pure execution allocates one complete descriptor per key, including ancestor
  records. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue.DescriptorMetadata

open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Semantics
open GraphQL.IncrementalDelivery.Semantics.OwnerPaths
  (mapNodes collectFields_supply collectSubfields_supply)

attribute [local simp] id_pure_eq id_bind_eq id_map_eq run_bind run_map

mutual
  /-- Plan execution retains complete descriptors in immediate and deferred work.
  Witness: sequential assignment extension through the two execution phases.
  -/
  theorem executePlan_descriptors (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variables : VariableValues) (fuel : Nat) (parentType : Name)
      (source : ResolverValue ObjectRef) (collection : FieldCollection)
      (path : ResponsePath) (usages : List Nat) (deferMap : DeferMap)
      (nodes : Assignment) (state : Nat)
      (hm : MapAt nodes state (getNewDeferMap collection.newDeferUsages path deferMap))
      : Completed nodes state
          ((executeExecutionPlan schema resolvers variables fuel parentType source
              collection.newDeferUsages
              (buildExecutionPlan collection.collectedFieldsMap usages) path usages
              deferMap).run
            state) := by
    obtain ⟨hle, middle, he, hw⟩ := executeCollectedFields_descriptors schema resolvers
      variables fuel
      parentType source _ path usages _ nodes state hm
    simp only [executeExecutionPlan, run_bind]
    split
    · exact ⟨hle, middle, he, hw⟩
    · obtain ⟨hlt, final, het, hwt⟩ := collectExecutionGroups_descriptors schema
        resolvers variables fuel
        parentType source _ path _ middle _ (hm.extend he hle)
      simp only [run_bind, StateT.run_pure, id_pure_eq]
      refine ⟨Nat.le_trans hle hlt, final, he.trans het hle, ?_⟩
      rw [WorkAt]
      exact ⟨hw.extend het hlt, hwt⟩
  termination_by (fuel, 6, 0, 0)
  decreasing_by
    all_goals simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right

  /-- Deferred partitions retain exact contributor and ancestor descriptors.
  Witness: defer-map lookup preserves metadata; later partitions extend the assignment.
  -/
  theorem collectExecutionGroups_descriptors (schema : Schema)
      (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
      (parentType : Name) (source : ResolverValue ObjectRef)
      (partitions : List (List Nat × CollectedFieldsMap)) (path : ResponsePath)
      (deferMap : DeferMap) (nodes : Assignment) (state : Nat)
      (hm : MapAt nodes state deferMap)
      : let output :=
          (collectExecutionGroups schema resolvers variables fuel parentType
            source partitions path deferMap).run
            state
        Output nodes state output.1 output.2 := by
    cases partitions with
    | nil =>
        simpa only [collectExecutionGroups, StateT.run_pure, id_pure_eq]
          using output_empty nodes state
    | cons partition rest =>
        rcases partition with ⟨usages, groups⟩
        obtain ⟨hle, middle, he, hw⟩ := executeCollectedFields_descriptors schema
          resolvers variables fuel
          parentType source groups path usages deferMap nodes state hm
        have hm' := hm.extend he hle
        obtain ⟨hlt, final, het, hwt⟩ := collectExecutionGroups_descriptors schema
          resolvers variables fuel
          parentType source rest path deferMap middle _ hm'
        simp only [collectExecutionGroups, executeExecutionGroup, run_bind,
          StateT.run_pure, id_pure_eq]
        refine ⟨Nat.le_trans hle hlt, final, he.trans het hle, ?_⟩
        simp only [WorkAt]
        exact ⟨⟨mapAt_filterMap (hm'.extend het hlt) usages, hw.extend het hlt⟩, hwt⟩
  termination_by (fuel, 5, 0, sizeOf partitions)
  decreasing_by
    all_goals subst_vars; simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right
    all_goals omega

  /-- Collected-field execution preserves exact descriptors across response assembly.
  Witness: list induction, composing allocation extensions and retained work certificates.
  -/
  theorem executeCollectedFields_descriptors (schema : Schema)
      (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
      (parentType : Name) (source : ResolverValue ObjectRef) (groups : CollectedFieldsMap)
      (path : ResponsePath) (usages : List Nat) (deferMap : DeferMap) (nodes : Assignment)
      (state : Nat) (hm : MapAt nodes state deferMap)
      : Completed nodes state
          ((executeCollectedFields schema resolvers variables fuel parentType source
              groups path usages deferMap).run
            state) := by
    cases groups with
    | nil =>
        simpa only [executeCollectedFields_nil, StateT.run_pure, id_pure_eq, Completed,
        Completion.pure] using output_empty nodes state
    | cons group rest =>
        rcases group with ⟨name, fields⟩
        obtain ⟨hle, middle, he, hw⟩ := executeResponseField_descriptors schema
          resolvers variables fuel
          parentType source name fields path usages deferMap nodes state hm
        obtain ⟨hlt, final, het, hwt⟩ := executeCollectedFields_descriptors schema
          resolvers variables fuel
          parentType source rest path usages deferMap middle _ (hm.extend he hle)
        simp only [executeCollectedFields_cons, run_bind, StateT.run_pure, id_pure_eq]
        exact ⟨Nat.le_trans hle hlt, final, he.trans het hle,
          workAt_completionCombine final _ List.append _ _ (hw.extend het hlt) hwt⟩
  termination_by (fuel, 4, 0, sizeOf groups)
  decreasing_by
    all_goals subst_vars; simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right
    all_goals omega

  /-- Field execution retains complete descriptors in its completed child work.
  Witness: schema/resolver case analysis followed by value completion.
  -/
  theorem executeResponseField_descriptors (schema : Schema)
      (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
      (parentType : Name) (source : ResolverValue ObjectRef) (name : Name)
      (fields : List FieldDetails) (path : ResponsePath) (usages : List Nat)
      (deferMap : DeferMap) (nodes : Assignment) (state : Nat)
      (hm : MapAt nodes state deferMap)
      : Completed nodes state
          ((executeResponseField schema resolvers variables fuel parentType source name
              fields path usages deferMap).run
            state) := by
    cases fuel with
    | zero => simpa only [executeResponseField, StateT.run_pure, id_pure_eq, Completed,
        Completion.error] using output_empty nodes state
    | succ fuel =>
        cases fields with
        | nil => simpa only [executeResponseField, StateT.run_pure, id_pure_eq, Completed,
            Completion.error] using output_empty nodes state
        | cons field rest =>
            simp only [executeResponseField]
            split
            · exact output_empty nodes state
            · split
              · exact output_empty nodes state
              · split
                · exact output_empty nodes state
                · obtain ⟨hle, next, he, hw⟩ := completeValue_descriptors schema
                    resolvers variables fuel _ _ _
                    (path ++ [.field name]) usages deferMap true nodes state hm
                  simp only [run_bind, StateT.run_pure, id_pure_eq]
                  exact ⟨hle, next, he, workAt_map next _ _ _ hw⟩
  termination_by (fuel, 3, 0, sizeOf fields)
  decreasing_by
    all_goals subst_vars; simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right

  /-- Value completion allocates coherent descriptors in all nested work.
  Witness: type/fuel induction; fresh subfield labels extend the existing assignment.
  -/
  theorem completeValue_descriptors (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variables : VariableValues) (fuel : Nat) (fieldType : TypeRef)
      (fields : List FieldDetails) (value : ResolverValue ObjectRef)
      (path : ResponsePath) (usages : List Nat) (deferMap : DeferMap)
      (allowStream : Bool) (nodes : Assignment) (state : Nat)
      (hm : MapAt nodes state deferMap)
      : Completed nodes state
          ((completeValue schema resolvers variables fuel fieldType fields value path
              usages deferMap allowStream).run
            state) := by
    cases fuel with
    | zero => simpa only [completeValue, StateT.run_pure, id_pure_eq, Completed,
        Completion.error] using output_empty nodes state
    | succ fuel =>
        cases fieldType with
        | nonNull inner =>
            obtain ⟨hle, next, he, hw⟩ := completeValue_descriptors schema resolvers
              variables (fuel + 1)
              inner fields value path usages deferMap allowStream nodes state hm
            simp only [completeValue, run_bind, StateT.run_pure, id_pure_eq]
            exact ⟨hle, next, he, workAt_nonNull next _ _ hw⟩
        | named parentType =>
            cases value with
            | null => simpa only [completeValue, StateT.run_pure, id_pure_eq, Completed,
                Completion.pure] using output_empty nodes state
            | scalar scalar =>
                simp only [completeValue]; split <;> exact output_empty nodes state
            | list items =>
                simpa only [completeValue, StateT.run_pure, id_pure_eq, Completed,
                Completion.error] using output_empty nodes state
            | object runtimeType ref =>
                simp only [completeValue]
                split
                · exact output_empty nodes state
                · have hs := collectSubfields_supply schema variables runtimeType
                    (.object runtimeType ref) fields state
                  obtain ⟨assigned, he, hn⟩ := mapAt_new nodes state _ path deferMap _
                    hm hs.1 hs.2
                    (collectSubfields_labels schema variables runtimeType
                      (.object runtimeType ref) fields state)
                  obtain ⟨hle, next, he', hw⟩ := executePlan_descriptors schema
                    resolvers variables fuel
                    runtimeType (.object runtimeType ref) _ path usages deferMap _ _ hn
                  simp only [run_bind, StateT.run_pure, id_pure_eq]
                  exact ⟨Nat.le_trans hs.1 hle, next, he.trans he' hs.1,
                    workAt_catchNull next _ _ _ hw⟩
        | list inner =>
            cases value with
            | null => simpa only [completeValue, StateT.run_pure, id_pure_eq, Completed,
                Completion.pure] using output_empty nodes state
            | scalar scalar =>
                simpa only [completeValue, StateT.run_pure, id_pure_eq, Completed,
                Completion.error] using output_empty nodes state
            | object runtimeType ref =>
                simpa only [completeValue, StateT.run_pure, id_pure_eq, Completed,
                Completion.error] using output_empty nodes state
            | list items =>
                simpa only [completeValue] using completeListValueWithStream_descriptors
                  schema
                  resolvers variables
                  fuel inner fields items path usages deferMap allowStream nodes state hm
  termination_by (fuel, 1, sizeOf fieldType, 0)
  decreasing_by
    all_goals subst_vars; simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right

  /-- Streaming completion extends the assignment with the exact stream descriptor.
  Witness: initial-list completion, fresh stream allocation, and successive item work.
  -/
  theorem completeListValueWithStream_descriptors (schema : Schema)
      (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
      (inner : TypeRef) (fields : List FieldDetails)
      (values : List (ResolverValue ObjectRef)) (path : ResponsePath) (usages : List Nat)
      (deferMap : DeferMap) (allowStream : Bool) (nodes : Assignment) (state : Nat)
      (hm : MapAt nodes state deferMap)
      : Completed nodes state
          ((completeListValueWithStream schema resolvers variables fuel inner fields
              values path usages deferMap allowStream).run
            state) := by
    unfold completeListValueWithStream
    dsimp only
    split
    · exact output_empty nodes state
    · obtain ⟨hle, next, he, hw⟩ := completeListValue_descriptors schema resolvers
        variables fuel inner
        fields values path 0 usages deferMap nodes state hm
      simp only [run_bind, StateT.run_pure, id_pure_eq]
      exact ⟨hle, next, he, workAt_catchNull next _ _ _ hw⟩
    · rename_i usage _
      obtain ⟨hle, middle, he, hw⟩ := completeListValue_descriptors schema resolvers
        variables fuel inner
        fields (values.take usage.initialCount) path 0 usages deferMap nodes state hm
      simp only [run_bind]
      split
      · exact ⟨hle, middle, he, workAt_catchNull middle _ _ _ hw⟩
      · split
        · exact ⟨hle, middle, he, workAt_catchNull middle _ _ _ hw⟩
        · let mid := ((completeListValue schema resolvers variables fuel inner fields
            (values.take usage.initialCount) path 0 usages deferMap).run state).2
          let node : DeliveryNode := {key := mid, path, label := usage.label}
          obtain ⟨hfresh, hnode⟩ := assigned_fresh middle mid node rfl
          obtain ⟨hlt, final, het, hitems⟩ := completeStreamItems_descriptors schema
            resolvers variables fuel
            inner (fields.map (fun field => {field with deferUsage := none}))
            (values.drop usage.initialCount) path usage.initialCount
            (fun key => if key = mid then node else middle key) (mid + 1)
          dsimp only [mid] at hlt
          simp only [freshExecutionKey, run_bind, StateT.run_get, StateT.run_set,
            StateT.run_pure, id_pure_eq]
          refine ⟨by omega, final, he.trans (hfresh.trans het (by omega)) hle, ?_⟩
          rw [WorkAt]
          refine ⟨(workAt_catchNull middle _ _ _ hw).extend (hfresh.trans het (by
            omega)) (by omega), ?_⟩
          rw [WorkAt]
          exact ⟨hnode.extend het hlt, hitems⟩
  termination_by (fuel, 3, 0, 0)
  decreasing_by
    all_goals subst_vars; simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right

  /-- Ordinary-list completion preserves descriptors across sequential items.
  Witness: list induction, transporting earlier item work through later allocations.
  -/
  theorem completeListValue_descriptors (schema : Schema)
      (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
      (itemType : TypeRef) (fields : List FieldDetails)
      (values : List (ResolverValue ObjectRef)) (path : ResponsePath) (index : Nat)
      (usages : List Nat) (deferMap : DeferMap) (nodes : Assignment) (state : Nat)
      (hm : MapAt nodes state deferMap)
      : Completed nodes state
          ((completeListValue schema resolvers variables fuel itemType fields values path
              index usages deferMap).run
            state) := by
    cases values with
    | nil => simpa only [completeListValue, StateT.run_pure, id_pure_eq, Completed,
        Completion.pure] using output_empty nodes state
    | cons value rest =>
        obtain ⟨hle, middle, he, hw⟩ := completeValue_descriptors schema resolvers
          variables fuel itemType fields
          value (path ++ [.index index]) usages deferMap false nodes state hm
        obtain ⟨hlt, final, het, hwt⟩ := completeListValue_descriptors schema resolvers
          variables fuel
          itemType fields rest path (index + 1) usages deferMap middle _ (hm.extend he
            hle)
        simp only [completeListValue, run_bind, StateT.run_pure, id_pure_eq]
        exact ⟨Nat.le_trans hle hlt, final, he.trans het hle,
          workAt_completionCombine final _ List.cons _ _ (hw.extend het hlt) hwt⟩
  termination_by (fuel, 2, sizeOf itemType, sizeOf values)
  decreasing_by
    all_goals subst_vars; simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right
    all_goals omega

  /-- Stream-tail completion preserves descriptors through all produced child work.
  Witness: each item starts with an empty defer map and extends the same assignment.
  -/
  theorem completeStreamItems_descriptors (schema : Schema)
      (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
      (itemType : TypeRef) (fields : List FieldDetails)
      (values : List (ResolverValue ObjectRef)) (path : ResponsePath) (index : Nat)
      (nodes : Assignment) (state : Nat)
      : ItemsOutput nodes state
          ((completeStreamItems schema resolvers variables fuel itemType fields values
              path index).run
            state) := by
    cases values with
    | nil =>
        simp only [completeStreamItems, StateT.run_pure, id_pure_eq]
        exact ⟨Nat.le_refl _, nodes, Extends.refl _ _, by simp [ItemsAt]⟩
    | cons value rest =>
        obtain ⟨hle, middle, he, hw⟩ := completeValue_descriptors schema resolvers
          variables fuel itemType
          fields value (path ++ [.index index]) [] [] false nodes state (by simp [MapAt,
            mapNodes])
        simp only [completeStreamItems, run_bind]
        split
        · exact ⟨hle, middle, he, by simp [ItemsAt, WorkAt]⟩
        · obtain ⟨hlt, final, het, hitems⟩ := completeStreamItems_descriptors schema
            resolvers variables fuel
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

/-- Root execution generates one complete descriptor assignment for all finite work.
Witness: fresh root collection initializes the map certificate and plan execution
  extends it.
-/
theorem executeRoot_descriptors (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues) (fuel : Nat) (parentType : Name)
    (source : ResolverValue ObjectRef) (selections : List Selection) (state : Nat)
    : ∃ nodes,
        WorkAt nodes
          ((executeRootSelectionSetCore schema resolvers variables fuel parentType source
              selections).run
            state).2
          ((executeRootSelectionSetCore schema resolvers variables fuel parentType source
              selections).run
            state).1.work := by
  have hs := collectFields_supply schema variables parentType source selections none state
  obtain ⟨assigned, _, hm⟩ := mapAt_new (fun key => ⟨key, [], none⟩) state _ [] [] _
    (by simp [MapAt, mapNodes]) hs.1 hs.2
    (collectFields_labels schema variables parentType source selections none state)
  obtain ⟨_, nodes, _, hw⟩ := executePlan_descriptors schema resolvers variables fuel
    parentType
    source _ [] [] [] _ _ hm
  exact ⟨nodes, hw⟩

end GraphQL.IncrementalDelivery.ReferenceWorkQueue.DescriptorMetadata
