import Proofs.GraphQL.IncrementalDelivery.Correctness.ScopeMetadata

/-! Pure execution preserves defer-ancestor scopes and fresh stream-item scope boundaries. -/

namespace GraphQL.IncrementalDelivery.Correctness.ScopeMetadata
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Semantics WorkQueueSemantics

variable {ObjectRef : Type}
attribute [local simp] id_pure_eq id_bind_eq id_map_eq run_bind run_map

/-- Certified item work also satisfies any enclosing lower scope bound.
Witness: list descent and upward weakening of each child's scope bound.
-/
theorem ItemsScoped.under {base path items} (certified : ItemsScoped path items)
    (below : base.IsPrefix path)
    : ItemsUnder base items := by
  induction items with
  | nil => trivial
  | cons entry rest ih => exact ⟨certified.1.2.mono below, ih certified.2⟩

-----------------------------------------------------------------------------------------
-- Scope coherence throughout execution
-----------------------------------------------------------------------------------------

mutual
  /-- Executing a plan preserves coherent node scopes between base and attachment.
  Witness: fresh-map construction, initial completion, and deferred partition execution.
  -/
  theorem executePlan_scopes (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variables : VariableValues) (fuel : Nat) (parentType : Name)
      (source : ResolverValue ObjectRef) (collection : FieldCollection)
      (path : ResponsePath) (usages : NodeRefs) (deferMap : DeferMap)
      (base : ResponsePath) (hm : MapAt base path deferMap) (below : base.IsPrefix path)
      : RunEnsures (Under base)
          (executeExecutionPlan schema resolvers variables fuel parentType source
            collection.newDeferUsages
            (buildExecutionPlan collection.collectedFieldsMap usages) path usages
            deferMap) := by
    have next := hm.new below collection.newDeferUsages
    simp only [executeExecutionPlan]
    refine runEnsures_bind (Under base) _ _ _ ?_ ?_
    · exact executeCollectedFields_scopes schema resolvers variables fuel parentType source
        _ path usages _ base next below
    · intro completed hc
      split
      · exact runEnsures_pure _ _ hc
      · refine runEnsures_bind (fun work => WorkScoped work ∧ ScopesUnder base work)
          _ _ _ ?_ ?_
        · exact collectExecutionGroups_scopes schema resolvers variables fuel parentType
            source _ path _ base next below
        · intro work hw
          apply runEnsures_pure
          refine ⟨⟨hc.1, ?_⟩, hc.2, ?_⟩
          · refine ⟨?_, hw.1⟩
            simpa only [List.filterMap_map, Function.comp_def]
              using next.1.filterMap (collection.newDeferUsages.map (·.ref))
          · refine ⟨?_, hw.2⟩
            simpa only [List.filterMap_map, Function.comp_def]
              using next.2.2.filterMap (collection.newDeferUsages.map (·.ref))
  termination_by (fuel, 6, 0, 0)
  decreasing_by
    all_goals simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right

  /-- Partition wrappers retain coherent map fragments and completed child scopes.
  Witness: partition-list induction; every wrapper uses filtered old map entries.
  -/
  theorem collectExecutionGroups_scopes (schema : Schema)
      (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
      (parentType : Name) (source : ResolverValue ObjectRef)
      (partitions : List (NodeRefs × CollectedFieldsMap)) (path : ResponsePath)
      (deferMap : DeferMap) (base : ResponsePath)
      (hm : MapAt base path deferMap) (below : base.IsPrefix path)
      : RunEnsures (fun work => WorkScoped work ∧ ScopesUnder base work)
          (collectExecutionGroups schema resolvers variables fuel parentType source
            partitions path deferMap) := by
    cases partitions with
    | nil => simp [collectExecutionGroups, RunEnsures, WorkScoped, ScopesUnder]
    | cons partition rest =>
        rcases partition with ⟨usages, groups⟩
        simp only [collectExecutionGroups, executeExecutionGroup]
        refine runEnsures_bind (Under base) _ _ _ ?_ ?_
        · exact executeCollectedFields_scopes schema resolvers variables fuel parentType
            source groups path usages deferMap base hm below
        · intro completed hc
          refine runEnsures_bind (fun work => WorkScoped work ∧ ScopesUnder base work)
            _ _ _ ?_ ?_
          · exact collectExecutionGroups_scopes schema resolvers variables fuel parentType
              source rest path deferMap base hm below
          · intro work hw
            exact runEnsures_pure _ _
              ⟨⟨⟨hm.1.filterMap usages, hc.1⟩, hw.1⟩,
                ⟨hm.2.2.filterMap usages, hc.2⟩, hw.2⟩
  termination_by (fuel, 5, 0, sizeOf partitions)
  decreasing_by
    all_goals subst_vars; simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right
    all_goals omega

  /-- Collected-field completion preserves coherent node scopes below base.
  Witness: field-list induction and scope-preserving completion combination.
  -/
  theorem executeCollectedFields_scopes (schema : Schema)
      (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
      (parentType : Name) (source : ResolverValue ObjectRef) (groups : CollectedFieldsMap)
      (path : ResponsePath) (usages : NodeRefs) (deferMap : DeferMap)
      (base : ResponsePath) (hm : MapAt base path deferMap) (below : base.IsPrefix path)
      : RunEnsures (Under base)
          (executeCollectedFields schema resolvers variables fuel parentType source groups
            path usages deferMap) := by
    cases groups with
    | nil =>
        simpa only [executeCollectedFields_nil] using runEnsures_pure _ _ (pure base
          ([] : List (Name × ResponseValue)))
    | cons group rest =>
        rcases group with ⟨name, fields⟩
        simp only [executeCollectedFields_cons]
        refine runEnsures_bind (Under base) _ _ _ ?_ ?_
        · exact executeResponseField_scopes schema resolvers variables fuel parentType source
            name fields path usages deferMap base hm below
        · intro head hh
          refine runEnsures_bind (Under base) _ _ _ ?_ ?_
          · exact executeCollectedFields_scopes schema resolvers variables fuel parentType
              source rest path usages deferMap base hm below
          · intro tail ht
            exact runEnsures_pure _ _ (combine base List.append head tail hh ht)
  termination_by (fuel, 4, 0, sizeOf groups)
  decreasing_by
    all_goals subst_vars; simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right
    all_goals try omega

  /-- Descending into a field keeps inherited scopes, rather than narrowing them to its
  task attachment. Witness: map upper-bound weakening and recursive value completion.
  -/
  theorem executeResponseField_scopes (schema : Schema)
      (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
      (parentType : Name) (source : ResolverValue ObjectRef) (name : Name)
      (fields : List FieldDetails) (path : ResponsePath)
      (usages : NodeRefs) (deferMap : DeferMap) (base : ResponsePath)
      (hm : MapAt base path deferMap) (below : base.IsPrefix path)
      : RunEnsures (Under base)
          (executeResponseField schema resolvers variables fuel parentType source name
            fields path usages deferMap) := by
    cases fuel with
    | zero =>
        simpa only [executeResponseField] using runEnsures_pure _ _ (error base 1)
    | succ fuel =>
        cases fields with
        | nil =>
            simpa only [executeResponseField] using runEnsures_pure _ _ (error base 1)
        | cons field rest =>
            simp only [executeResponseField]
            split
            · exact runEnsures_pure _ _ (error base 1)
            · split
              · exact runEnsures_pure _ _ (show Under base _ from ⟨trivial, trivial⟩)
              · split
                · exact runEnsures_pure _ _ (show Under base _ from ⟨trivial, trivial⟩)
                · refine runEnsures_bind (Under base) _ _ _ ?_ ?_
                  · exact completeValue_scopes schema resolvers variables fuel _ _ _
                      (path ++ [.field name]) usages deferMap true base
                      (hm.below ⟨[.field name], rfl⟩) (below.trans ⟨[.field name], rfl⟩)
                  · intro completed hc
                    exact runEnsures_pure _ _ (map base _ completed hc)
  termination_by (fuel, 3, 0, sizeOf fields)
  decreasing_by
    all_goals subst_vars; simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right

  /-- Value completion preserves coherent node scopes below its enclosing base.
  Witness: fuel/type descent, inherited-map object collection, and indexed list completion.
  -/
  theorem completeValue_scopes (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variables : VariableValues) (fuel : Nat) (fieldType : TypeRef)
      (fields : List FieldDetails) (value : ResolverValue ObjectRef)
      (path : ResponsePath) (usages : NodeRefs) (deferMap : DeferMap) (allowStream : Bool)
      (base : ResponsePath) (hm : MapAt base path deferMap) (below : base.IsPrefix path)
      : RunEnsures (Under base)
          (completeValue schema resolvers variables fuel fieldType fields value path
            usages deferMap allowStream) := by
    cases fuel with
    | zero =>
        simpa only [completeValue] using runEnsures_pure _ _ (error base 1)
    | succ fuel =>
        cases fieldType with
        | nonNull inner =>
            simp only [completeValue]
            refine runEnsures_bind (Under base) _ _ _ ?_ ?_
            · exact completeValue_scopes schema resolvers variables (fuel + 1) inner fields
                value path usages deferMap allowStream base hm below
            · intro completed hc
              exact runEnsures_pure _ _ (nonNull base completed hc)
        | named parentType =>
            cases value with
            | null =>
                simpa only [completeValue] using runEnsures_pure _ _
                  (pure base ResponseValue.null)
            | scalar scalar =>
                simp only [completeValue]
                split
                · exact runEnsures_pure _ _ (error base 1)
                · exact runEnsures_pure _ _ (pure base _)
            | list items =>
                simpa only [completeValue] using runEnsures_pure _ _ (error base 1)
            | object runtimeType ref =>
                simp only [completeValue]
                split
                · exact runEnsures_pure _ _ (error base 1)
                · refine runEnsures_bind (fun _ : FieldCollection => True) _ _ _
                    (fun _ => trivial) ?_
                  intro collection _
                  refine runEnsures_bind (Under base) _ _ _ ?_ ?_
                  · exact executePlan_scopes schema resolvers variables fuel runtimeType
                      (.object runtimeType ref) collection path usages deferMap base hm below
                  · intro completed hc
                    exact runEnsures_pure _ _ (catchNull base _ completed hc)
        | list inner =>
            cases value with
            | null =>
                simpa only [completeValue] using runEnsures_pure _ _
                  (pure base ResponseValue.null)
            | scalar scalar =>
                simpa only [completeValue] using runEnsures_pure _ _ (error base 1)
            | object runtimeType ref =>
                simpa only [completeValue] using runEnsures_pure _ _ (error base 1)
            | list items =>
                simpa only [completeValue] using completeListValueWithStream_scopes
                  schema resolvers variables fuel inner fields items path usages deferMap
                  allowStream base hm below
  termination_by (fuel, 1, sizeOf fieldType, 0)
  decreasing_by
    all_goals subst_vars; simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right

  /-- Stream hooks establish fresh child scopes below the list boundary, including empty
  tails. Witness: the stream's empty inherited defer map and certified item completions.
  -/
  theorem completeListValueWithStream_scopes (schema : Schema)
      (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
      (inner : TypeRef) (fields : List FieldDetails)
      (values : List (ResolverValue ObjectRef)) (path : ResponsePath)
      (usages : NodeRefs) (deferMap : DeferMap) (allowStream : Bool) (base : ResponsePath)
      (hm : MapAt base path deferMap) (below : base.IsPrefix path)
      : RunEnsures (Under base)
          (completeListValueWithStream schema resolvers variables fuel inner fields
            values path usages deferMap allowStream) := by
    unfold completeListValueWithStream
    dsimp only
    split
    · exact runEnsures_pure _ _ ⟨trivial, trivial⟩
    · refine runEnsures_bind (Under base) _ _ _ ?_ ?_
      · exact completeListValue_scopes schema resolvers variables fuel inner fields
          values path 0 usages deferMap base hm below
      · intro completed hc
        exact runEnsures_pure _ _ (catchNull base _ completed hc)
    · rename_i usage _
      refine runEnsures_bind (Under base) _ _ _ ?_ ?_
      · exact completeListValue_scopes schema resolvers variables fuel inner fields
          (values.take usage.initialCount) path 0 usages deferMap base hm below
      · intro initial hi
        split
        · exact runEnsures_pure _ _ (catchNull base _ initial hi)
        · split
          · exact runEnsures_pure _ _ (catchNull base _ initial hi)
          · refine runEnsures_bind (fun _ : NodeRef => True) _ _ _ (fun _ => trivial) ?_
            intro ref _
            refine runEnsures_bind (ItemsScoped path) _ _ _ ?_ ?_
            · exact completeStreamItems_scopes schema resolvers variables fuel inner
                _ _ path usage.initialCount
            · intro tail ht
              have initial := catchNull base ResponseValue.list initial hi
              exact runEnsures_pure _ _
                ⟨⟨initial.1, ht⟩, initial.2, below, ht.under below⟩
  termination_by (fuel, 3, 0, 0)
  decreasing_by
    all_goals subst_vars; simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right

  /-- Ordinary list completion preserves inherited scopes while item attachments descend.
  Witness: list induction and upper-bound weakening of the inherited defer map.
  -/
  theorem completeListValue_scopes (schema : Schema)
      (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
      (itemType : TypeRef) (fields : List FieldDetails)
      (values : List (ResolverValue ObjectRef)) (path : ResponsePath) (index : Nat)
      (usages : NodeRefs) (deferMap : DeferMap) (base : ResponsePath)
      (hm : MapAt base path deferMap) (below : base.IsPrefix path)
      : RunEnsures (Under base)
          (completeListValue schema resolvers variables fuel itemType fields values path
            index usages deferMap) := by
    cases values with
    | nil =>
        simpa only [completeListValue] using runEnsures_pure _ _
          (pure base ([] : List ResponseValue))
    | cons value rest =>
        simp only [completeListValue]
        refine runEnsures_bind (Under base) _ _ _ ?_ ?_
        · exact completeValue_scopes schema resolvers variables fuel itemType fields value
            (path ++ [.index index]) usages deferMap false base
            (hm.below ⟨[.index index], rfl⟩) (below.trans ⟨[.index index], rfl⟩)
        · intro head hh
          refine runEnsures_bind (Under base) _ _ _ ?_ ?_
          · exact completeListValue_scopes schema resolvers variables fuel itemType fields
              rest path (index + 1) usages deferMap base hm below
          · intro tail ht
            exact runEnsures_pure _ _ (combine base List.cons head tail hh ht)
  termination_by (fuel, 2, sizeOf itemType, sizeOf values)
  decreasing_by
    all_goals subst_vars; simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right
    all_goals try omega

  /-- Streamed items allocate coherent scopes beneath their list's attachment.
  Witness: each item resets the inherited map; failure retains no child work.
  -/
  theorem completeStreamItems_scopes (schema : Schema)
      (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
      (itemType : TypeRef) (fields : List FieldDetails)
      (values : List (ResolverValue ObjectRef)) (path : ResponsePath) (index : Nat)
      : RunEnsures (ItemsScoped path)
          (completeStreamItems schema resolvers variables fuel itemType fields values
            path index) := by
    cases values with
    | nil => simp [completeStreamItems, RunEnsures, ItemsScoped]
    | cons value rest =>
        simp only [completeStreamItems]
        refine runEnsures_bind (Under path) _ _ _ ?_ ?_
        · exact completeValue_scopes schema resolvers variables fuel itemType fields value
            (path ++ [.index index]) [] [] false path (by simp [MapAt, MapScoped,
              MapBelow, MapUnder, OwnerPaths.mapNodes]) ⟨[.index index], rfl⟩
        · intro head hh
          split
          · exact runEnsures_pure _ _ ⟨⟨trivial, trivial⟩, trivial⟩
          · refine runEnsures_bind (ItemsScoped path) _ _ _ ?_ ?_
            · exact completeStreamItems_scopes schema resolvers variables fuel itemType
                fields rest path (index + 1)
            · intro tail ht
              exact runEnsures_pure _ _ ⟨hh, ht⟩
  termination_by (fuel, 2, sizeOf itemType, sizeOf values)
  decreasing_by
    all_goals subst_vars; simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right
    all_goals omega
end

/-- Every root completion has coherent defer-ancestor and stream-item node scopes.
Witness: root collection, the empty map, and mutual execution-scope preservation.
No event history, failure report, or producer-attachment/group-scope equality is assumed.
-/
theorem executeRootSelectionSetCore_scopes (schema : Schema)
    (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
    (parentType : Name) (source : ResolverValue ObjectRef) (selections : List Selection)
    : RunEnsures (Under [])
        (executeRootSelectionSetCore schema resolvers variables fuel parentType source
          selections) := by
  simp only [executeRootSelectionSetCore]
  refine runEnsures_bind (fun _ : FieldCollection => True) _ _ _ (fun _ => trivial) ?_
  intro collection _
  exact executePlan_scopes schema resolvers variables fuel parentType source collection
    [] [] [] [] (by simp [MapAt, MapScoped, MapBelow, MapUnder, OwnerPaths.mapNodes])
    ⟨[], rfl⟩

end GraphQL.IncrementalDelivery.Correctness.ScopeMetadata
