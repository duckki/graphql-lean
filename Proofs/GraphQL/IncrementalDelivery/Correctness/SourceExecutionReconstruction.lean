import Proofs.GraphQL.IncrementalDelivery.Correctness.SourceListReconstruction
import Proofs.GraphQL.IncrementalDelivery.Correctness.BasicFieldPartitions

/-! Complete successful mixed source work reconstructs directive-erased basic
execution. Success is internal and must be derived from the actual complete,
error-free trace; no successful-step assumption is added to public semantics.
-/

namespace GraphQL.IncrementalDelivery.Correctness.SourceReconstruction

open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Semantics
open TypedResponse
open MixedPaths (WorkCursorSeed ItemCursorSeed resultCursors)
open ResponsePositions (Cursors fieldCursors listCursors itemCursors)

attribute [local simp] id_pure_eq id_bind_eq id_map_eq run_bind run_map

mutual
  /-- Plan execution reconstructs all collected groups, using partition permutation and
  the mutual execution witnesses. -/
  theorem executePlan_seeded (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variables : VariableValues) (fuel : Nat) (parentType : Name)
      (source : ResolverValue ObjectRef) (collection : FieldCollection)
      (path : ResponsePath) (usages : List Nat) (deferMap : DeferMap)
      : RunEnsures
          (SeededReconstructs (fields path) (fieldCursors path)
            (GraphQL.Execution.executeCollectedFields schema resolvers variables fuel
              parentType source (eraseGroups collection.fields)))
          (executeExecutionPlan schema resolvers variables fuel parentType source
            collection.newDeferUsages (buildExecutionPlan collection.fields usages)
            path usages deferMap) := by
    let plan := buildExecutionPlan collection.fields usages
    simp only [executeExecutionPlan]
    refine runEnsures_bind
      (SeededReconstructs (fields path) (fieldCursors path)
        (GraphQL.Execution.executeCollectedFields schema resolvers variables fuel
          parentType source (eraseGroups plan.collectedFieldsMap)))
      _ _ _ ?_ ?_
    · exact executeCollectedFields_seeded schema resolvers variables fuel parentType source _ path usages _
    · intro initial hi
      split
      · rename_i errors he
        apply runEnsures_pure
        refine ⟨hi.positive, ?_⟩
        simp [CompletionSuccess, he]
      · refine runEnsures_bind
          (SeededWorkReconstructs path
            (GraphQL.Execution.executeCollectedFields schema resolvers variables fuel
              parentType source
              (eraseGroups (plan.newCollectedFieldsMaps.flatMap Prod.snd))))
          _ _ _ ?_ ?_
        · exact collectExecutionGroups_seeded schema resolvers variables fuel parentType source _ path _
        · intro tasks ht
          apply runEnsures_pure
          refine ⟨hi.positive, ?_⟩
          intro hs
          obtain ⟨initialData, si, hiData, his, hip, hiseed⟩ := hi.reconstruct ⟨hs.1, hs.2.1⟩
          obtain ⟨taskData, st, htData, hts, htp, htseed⟩ := ht hs.2.2
          have hb := basicFields_append schema resolvers variables fuel parentType source
            _ _ initialData taskData hiData htData
          have hpall := buildExecutionPlan_erasure_perm collection.fields usages
          have hcombined : GraphQL.Execution.executeCollectedFields schema resolvers variables fuel parentType source
              (eraseGroups (executionPlanGroups plan)) = .ok (initialData ++ taskData, 0) := by
            simpa [executionPlanGroups, eraseGroups] using hb
          obtain ⟨data, hd, hpd⟩ := basicFields_perm schema resolvers variables fuel parentType source path
            _ _ hpall _ hcombined
          refine ⟨data, si ++ st, hd, .combine his hts, ?_, ?_⟩
          · apply List.Perm.trans _ hpd
            simpa only [List.flatten_append, TypedResponse.fields_append, List.append_assoc] using hip.append htp
          · intro hn
            have hn' : (((result (fields path) initial.result ++ si.flatten) ++ st.flatten).map Prod.fst).Nodup := by
              simpa only [List.flatten_append, List.append_assoc] using hn
            have hparts := List.nodup_append.mp (by simpa only [List.map_append] using hn')
            simpa only [entryPaths, List.map_append]
              using WorkCursorSeed.combine
                (hiseed (by simpa only [List.map_append] using hparts.1))
                (htseed _ hparts.2.1)
  termination_by (fuel, 6, 0, 0)
  decreasing_by
    all_goals simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right

  /-- Deferred partitions reconstruct their basic fields, by partition induction with
  retained child work. -/
  theorem collectExecutionGroups_seeded (schema : Schema)
      (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
      (parentType : Name) (source : ResolverValue ObjectRef)
      (partitions : List (List Nat × CollectedFieldsMap)) (path : ResponsePath)
      (deferMap : DeferMap)
      : RunEnsures
          (SeededWorkReconstructs path
            (GraphQL.Execution.executeCollectedFields schema resolvers variables fuel
              parentType source (eraseGroups (partitions.flatMap Prod.snd))))
          (collectExecutionGroups schema resolvers variables fuel parentType source
            partitions path deferMap) := by
    cases partitions with
    | nil =>
        simp only [collectExecutionGroups]
        apply runEnsures_pure
        intro _
        exact ⟨
          [],
          [],
          by simp [eraseGroups, GraphQL.Execution.executeCollectedFields],
          .empty,
          .refl _,
          fun _ _ => .empty
        ⟩
    | cons partition rest =>
        rcases partition with ⟨usages, groups⟩
        simp only [collectExecutionGroups, executeExecutionGroup]
        refine runEnsures_bind
          (SeededReconstructs (fields path) (fieldCursors path)
            (GraphQL.Execution.executeCollectedFields schema resolvers variables fuel
              parentType source (eraseGroups groups)))
          _ _ _ ?_ ?_
        · exact executeCollectedFields_seeded schema resolvers variables fuel parentType source groups path usages deferMap
        · intro completed hc
          refine runEnsures_bind
            (SeededWorkReconstructs path
              (GraphQL.Execution.executeCollectedFields schema resolvers variables fuel
                parentType source (eraseGroups (rest.flatMap Prod.snd))))
            _ _ _ ?_ ?_
          · exact collectExecutionGroups_seeded schema resolvers variables fuel parentType source rest path deferMap
          · intro tasks ht
            apply runEnsures_pure
            intro hs
            obtain ⟨head, sh, hh, hsh, hhp, hseedh⟩ := hc.reconstruct hs.1
            obtain ⟨tail, st, htail, hst, htailp, hseedt⟩ := ht hs.2
            refine ⟨head ++ tail, _, ?_, .combine (.executionGroup hsh) hst, ?_, ?_⟩
            · simpa [eraseGroups] using basicFields_append schema resolvers variables fuel parentType source
                _ _ head tail hh htail
            · simpa only [List.flatten_append, List.flatten_cons, TypedResponse.fields_append] using hhp.append htailp
            · intro cursors hn
              have hn' : (((result (fields path) completed.result ++ sh.flatten) ++ st.flatten).map Prod.fst).Nodup := by
                simpa only [List.flatten_append, List.flatten_cons] using hn
              have hparts := List.nodup_append.mp (by simpa only [List.map_append] using hn')
              simpa only [entryPaths, List.map_append, List.map_cons, result_fields_paths]
                using WorkCursorSeed.combine
                  (WorkCursorSeed.executionGroup
                    (hseedh (by simpa only [List.map_append] using hparts.1)))
                  (hseedt cursors hparts.2.1)
  termination_by (fuel, 5, 0, sizeOf partitions)
  decreasing_by
    all_goals subst_vars; simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right
    all_goals omega

  /-- Collected fields reconstruct basic execution, by successful head/tail
  combination. -/
  theorem executeCollectedFields_seeded (schema : Schema)
      (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
      (parentType : Name) (source : ResolverValue ObjectRef) (groups : CollectedFieldsMap)
      (path : ResponsePath) (usages : List Nat) (deferMap : DeferMap)
      : RunEnsures
          (SeededReconstructs (fields path) (fieldCursors path)
            (GraphQL.Execution.executeCollectedFields schema resolvers variables fuel
              parentType source (eraseGroups groups)))
          (executeCollectedFields schema resolvers variables fuel parentType source groups
            path usages deferMap) := by
    cases groups with
    | nil =>
        simp only [executeCollectedFields_nil, eraseGroups, List.map_nil, GraphQL.Execution.executeCollectedFields]
        exact runEnsures_pure _ _ (seeded_pure _ _ _)
    | cons group rest =>
        rcases group with ⟨name, selected⟩
        simp only [executeCollectedFields_cons, eraseGroups, List.map_cons, eraseGroup, GraphQL.Execution.executeCollectedFields]
        refine runEnsures_bind (SeededReconstructs (fields path) (fieldCursors path)
          (GraphQL.Execution.executeField schema resolvers variables fuel parentType source name
            (selected.map eraseField))) _ _ _ ?_ ?_
        · exact executeResponseField_seeded schema resolvers variables fuel parentType source name selected path usages deferMap
        · intro head hh
          refine runEnsures_bind (SeededReconstructs (fields path) (fieldCursors path)
            (GraphQL.Execution.executeCollectedFields schema resolvers variables fuel parentType source
              (eraseGroups rest))) _ _ _ ?_ ?_
          · exact executeCollectedFields_seeded schema resolvers variables fuel parentType source rest path usages deferMap
          · intro tail ht
            exact runEnsures_pure _ _ (seeded_combine (TypedResponse.fields_append path)
              (fieldCursors_append path) (fieldCursors_history path) (fieldCursors_history path) hh ht)
  termination_by (fuel, 4, 0, sizeOf groups)
  decreasing_by
    all_goals subst_vars; simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right
    all_goals omega

  /-- Field resolution and completion reconstruct basic entries, by lookup and resolver
  cases. -/
  theorem executeResponseField_seeded (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variables : VariableValues) (fuel : Nat) (parentType : Name)
      (source : ResolverValue ObjectRef) (name : Name) (selected : List ExecutableField)
      (path : ResponsePath) (usages : List Nat) (deferMap : DeferMap)
      : RunEnsures
          (SeededReconstructs (fields path) (fieldCursors path)
            (GraphQL.Execution.executeField schema resolvers variables fuel parentType
              source name (selected.map eraseField)))
          (executeResponseField schema resolvers variables fuel parentType source name
            selected path usages deferMap) := by
    cases fuel with
    | zero =>
        simp only [executeResponseField]
        exact runEnsures_pure _ _ (seeded_error _ _ _ _ (by omega))
    | succ fuel =>
        cases selected with
        | nil =>
            simp only [executeResponseField]
            exact runEnsures_pure _ _ (seeded_error _ _ _ _ (by omega))
        | cons field rest =>
            cases hf : schema.lookupField parentType field.fieldName with
            | none =>
                simp only [executeResponseField, hf]
                exact runEnsures_pure _ _ (seeded_error _ _ _ _ (by omega))
            | some definition =>
                cases ha
                      : coerceArgumentValues schema variables definition.arguments
                          field.arguments with
                | error =>
                    simp only [executeResponseField, hf, ha]
                    exact runEnsures_pure _ _ (seeded_failedField _ _ _ _)
                | success arguments =>
                    cases hr
                          : resolveFieldValue resolvers parentType field.fieldName
                              arguments source with
                    | none =>
                        simp only [executeResponseField, hf, ha, hr]
                        exact runEnsures_pure _ _ (seeded_failedField _ _ _ _)
                    | some resolved =>
                        simp only [executeResponseField, List.map_cons, GraphQL.Execution.executeField, eraseField, hf, ha, hr]
                        refine runEnsures_bind (SeededReconstructs (value (path ++ [.field name])) (listCursors (path ++ [.field name]))
                          (GraphQL.Execution.completeValue schema resolvers variables fuel definition.outputType
                            ((field :: rest).map eraseField) resolved)) _ _ _ ?_ ?_
                        · exact completeValue_seeded schema resolvers variables fuel _ _ _
                            (path ++ [.field name]) usages deferMap true
                        · intro completed hc
                          exact runEnsures_pure _ _ (seeded_field path name hc)
  termination_by (fuel, 3, 0, sizeOf selected)
  decreasing_by
    all_goals subst_vars; simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right

  /-- Mixed value completion reconstructs basic values, by mutual fuel/type descent. -/
  theorem completeValue_seeded (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variables : VariableValues) (fuel : Nat) (fieldType : TypeRef)
      (selected : List ExecutableField) (resolved : ResolverValue ObjectRef)
      (path : ResponsePath) (usages : List Nat) (deferMap : DeferMap) (allowStream : Bool)
      : RunEnsures
          (SeededReconstructs (value path) (listCursors path)
            (GraphQL.Execution.completeValue schema resolvers variables fuel fieldType
              (selected.map eraseField) resolved))
          (completeValue schema resolvers variables fuel fieldType selected resolved path
            usages deferMap allowStream) := by
    cases fuel with
    | zero =>
        simp only [completeValue]
        exact runEnsures_pure _ _ (seeded_error _ _ _ _ (by omega))
    | succ fuel =>
        cases fieldType with
        | nonNull inner =>
            simp only [completeValue, GraphQL.Execution.completeValue]
            refine runEnsures_bind (SeededReconstructs (value path) (listCursors path)
              (GraphQL.Execution.completeValue schema resolvers variables (fuel + 1) inner
                (selected.map eraseField) resolved)) _ _ _ ?_ ?_
            · exact completeValue_seeded schema resolvers variables (fuel + 1) inner selected resolved path usages deferMap allowStream
            · intro completed hc
              exact runEnsures_pure _ _ (seeded_nonNull path hc)
        | named parentType =>
            cases resolved with
            | null =>
                simp only [completeValue, GraphQL.Execution.completeValue]
                exact runEnsures_pure _ _ (seeded_pure _ _ _)
            | scalar scalar =>
                simp only [completeValue, GraphQL.Execution.completeValue]
                split
                · exact runEnsures_pure _ _ (seeded_error _ _ _ _ (by omega))
                · exact runEnsures_pure _ _ (seeded_pure _ _ _)
            | list data =>
                simp only [completeValue]
                exact runEnsures_pure _ _ (seeded_error _ _ _ _ (by omega))
            | object runtimeType ref =>
                cases ht : schema.typeIncludesObjectBool parentType runtimeType <;>
                  simp only [completeValue, GraphQL.Execution.completeValue, ht,
                    Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
                · exact runEnsures_pure _ _ (seeded_error _ _ _ _ (by omega))
                · refine runEnsures_bind (fun collection => eraseGroups collection.fields =
                    GraphQL.Execution.collectSubfields schema variables runtimeType (.object runtimeType ref)
                      (selected.map eraseField)) _ _ _ ?_ ?_
                  · exact collectSubfields_erase schema variables runtimeType (.object runtimeType ref) selected
                  · intro collection hc
                    refine runEnsures_bind (SeededReconstructs (fields path) (fieldCursors path)
                      (GraphQL.Execution.executeCollectedFields schema resolvers variables fuel runtimeType
                        (.object runtimeType ref) (GraphQL.Execution.collectSubfields schema variables runtimeType
                          (.object runtimeType ref) (selected.map eraseField)))) _ _ _ ?_ ?_
                    · simpa only [hc] using executePlan_seeded schema resolvers variables fuel runtimeType
                        (.object runtimeType ref) collection path usages deferMap
                    · intro completed hv
                      exact runEnsures_pure _ _ (seeded_catchNull path .object (fun _ => rfl) (fun _ _ _ h => h) hv)
        | list inner =>
            cases resolved with
            | null =>
                simp only [completeValue, GraphQL.Execution.completeValue]
                exact runEnsures_pure _ _ (seeded_pure _ _ _)
            | scalar scalar =>
                simp only [completeValue]
                exact runEnsures_pure _ _ (seeded_error _ _ _ _ (by omega))
            | object runtimeType ref =>
                simp only [completeValue]
                exact runEnsures_pure _ _ (seeded_error _ _ _ _ (by omega))
            | list data =>
                simpa only [completeValue, GraphQL.Execution.completeValue]
                  using completeListValueWithStream_seeded schema resolvers variables fuel
                    inner selected data path usages deferMap allowStream
  termination_by (fuel, 1, sizeOf fieldType, 0)
  decreasing_by
    all_goals subst_vars; simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right

  /-- Stream-aware completion reconstructs the basic list, by exact prefix/suffix
  splitting. -/
  theorem completeListValueWithStream_seeded (schema : Schema)
      (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
      (inner : TypeRef) (selected : List ExecutableField)
      (values : List (ResolverValue ObjectRef)) (path : ResponsePath) (usages : List Nat)
      (deferMap : DeferMap) (allowStream : Bool)
      : RunEnsures
          (SeededReconstructs (value path) (listCursors path)
            (GraphQL.Execution.catchBubbleAsNull ResponseValue.list
              (GraphQL.Execution.completeValueList schema resolvers variables fuel inner
                (selected.map eraseField) values)))
          (completeListValueWithStream schema resolvers variables fuel inner selected
            values path usages deferMap allowStream) := by
    unfold completeListValueWithStream
    dsimp only
    split
    · rename_i errors he
      have herr : errors = 1 := by
        cases allowStream with
        | false => simp at he
        | true => exact getStreamUsage_error_count variables _ errors he
      subst errors
      apply runEnsures_pure
      refine ⟨by simp [BasicErrors.PositiveFailure], ?_⟩
      simp [CompletionSuccess]
    · refine runEnsures_bind (SeededReconstructs (items path 0) (itemCursors path 0)
        (GraphQL.Execution.completeValueList schema resolvers variables fuel inner (selected.map eraseField) values)) _ _ _ ?_ ?_
      · exact completeListValue_seeded schema resolvers variables fuel inner selected values path 0 usages deferMap
      · intro completed hc
        exact runEnsures_pure _ _ (seeded_catchNull path .list (fun _ => rfl) (list_cursors_extend path) hc)
    · rename_i usage _
      refine runEnsures_bind
        (fun completed =>
          SeededReconstructs (items path 0) (itemCursors path 0)
            (GraphQL.Execution.completeValueList schema resolvers variables fuel inner
              (selected.map eraseField) (values.take usage.initialCount)) completed
          ∧ ∀ data errors,
              completed.result = .ok (data, errors)
              → data.length = (values.take usage.initialCount).length)
        _ _ _ ?_ ?_
      · intro state
        exact ⟨completeListValue_seeded schema resolvers variables fuel inner selected _ path 0 usages deferMap state,
          fun data errors he => MixedPaths.completeListValue_result_length schema resolvers variables fuel inner selected
            (values.take usage.initialCount) path 0 usages deferMap state data errors he⟩
      · intro initial his
        obtain ⟨hi, hilength⟩ := his
        split
        · rename_i errors he
          apply runEnsures_pure
          refine ⟨by simp [BasicErrors.PositiveFailure, Completion.catchNull, he], ?_⟩
          intro hs
          have hp := hi.positive errors he
          simp [CompletionSuccess, Completion.catchNull, he] at hs
          omega
        · rename_i data he
          split
          · rename_i hempty
            have htake : values.take usage.initialCount = values :=
              List.take_of_length_le (by omega)
            apply runEnsures_pure
            simpa only [htake]
              using seeded_catchNull path .list (fun _ => rfl) (list_cursors_extend path)
                hi
          · rename_i hnonempty
            refine runEnsures_bind (fun _ : Nat => True) _ _ _ (fun _ => trivial) ?_
            intro key _
            refine runEnsures_bind (SeededItemsReconstructs path usage.initialCount
              (GraphQL.Execution.completeValueList schema resolvers variables fuel inner
                (selected.map eraseField) (values.drop usage.initialCount))) _ _ _ ?_ ?_
            · simpa only [eraseFields_clearDefer] using completeStreamItems_seeded schema resolvers variables fuel inner
                (selected.map (fun field => {field with deferUsage := none})) _ path usage.initialCount
            · intro tail ht
              apply runEnsures_pure
              have hall := seeded_stream path usage.initialCount hi ht data.1 data.2 he
                (by
                  have hl := hilength data.1 data.2 he
                  have hb : usage.initialCount ≤ values.length := by omega
                  simpa only [List.length_take, Nat.min_eq_left hb] using hl)
                (basicPrefix_length schema resolvers variables fuel inner (selected.map eraseField) values
                  usage.initialCount (by omega))
                {key := key, path := path, label := usage.label} rfl
              have hb := basicCompleteValueList_append schema resolvers variables fuel inner (selected.map eraseField)
                (values.take usage.initialCount) (values.drop usage.initialCount)
              rw [List.take_append_drop] at hb
              simpa only [← hb] using hall
  termination_by (fuel, 3, 0, 0)
  decreasing_by
    all_goals subst_vars; simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right

  /-- Ordinary list completion reconstructs each item at its index, by list descent. -/
  theorem completeListValue_seeded (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variables : VariableValues) (fuel : Nat) (itemType : TypeRef)
      (selected : List ExecutableField) (data : List (ResolverValue ObjectRef))
      (path : ResponsePath) (index : Nat) (usages : List Nat) (deferMap : DeferMap)
      : RunEnsures
          (SeededReconstructs (items path index) (itemCursors path index)
            (GraphQL.Execution.completeValueList schema resolvers variables fuel itemType
              (selected.map eraseField) data))
          (completeListValue schema resolvers variables fuel itemType selected data path
            index usages deferMap) := by
    cases data with
    | nil =>
        simp only [completeListValue, GraphQL.Execution.completeValueList]
        exact runEnsures_pure _ _ (seeded_pure _ _ _)
    | cons resolved rest =>
        simp only [completeListValue, GraphQL.Execution.completeValueList]
        refine runEnsures_bind (SeededReconstructs (value (path ++ [.index index])) (listCursors (path ++ [.index index]))
          (GraphQL.Execution.completeValue schema resolvers variables fuel itemType (selected.map eraseField) resolved)) _ _ _ ?_ ?_
        · exact completeValue_seeded schema resolvers variables fuel itemType selected resolved
            (path ++ [.index index]) usages deferMap false
        · intro head hh
          refine runEnsures_bind (SeededReconstructs (items path (index + 1)) (itemCursors path (index + 1))
            (GraphQL.Execution.completeValueList schema resolvers variables fuel itemType (selected.map eraseField) rest)) _ _ _ ?_ ?_
          · exact completeListValue_seeded schema resolvers variables fuel itemType selected rest path (index + 1) usages deferMap
          · intro tail ht
            exact runEnsures_pure _ _ (seeded_combine (fun _ _ => rfl) (fun _ _ => rfl)
              (listCursors_history (path ++ [.index index])) (itemCursors_history path (index + 1)) hh ht)
  termination_by (fuel, 2, sizeOf itemType, sizeOf data)
  decreasing_by
    all_goals subst_vars; simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right
    all_goals omega

  /-- Successful retained stream items reconstruct the complete suffix, by item
  descent. -/
  theorem completeStreamItems_seeded (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variables : VariableValues) (fuel : Nat) (itemType : TypeRef)
      (selected : List ExecutableField) (values : List (ResolverValue ObjectRef))
      (path : ResponsePath) (index : Nat)
      : RunEnsures
          (SeededItemsReconstructs path index
            (GraphQL.Execution.completeValueList schema resolvers variables fuel itemType
              (selected.map eraseField) values))
          (completeStreamItems schema resolvers variables fuel itemType selected values
            path index) := by
    cases values with
    | nil =>
        simp only [completeStreamItems]
        exact runEnsures_pure _ _
          (fun _ =>
            ⟨
              [],
              [],
              by simp [GraphQL.Execution.completeValueList],
              .nil,
              .refl _,
              fun _ => .nil
            ⟩)
    | cons resolved rest =>
        simp only [completeStreamItems, GraphQL.Execution.completeValueList]
        refine runEnsures_bind (SeededReconstructs (value (path ++ [.index index])) (listCursors (path ++ [.index index]))
          (GraphQL.Execution.completeValue schema resolvers variables fuel itemType (selected.map eraseField) resolved)) _ _ _ ?_ ?_
        · exact completeValue_seeded schema resolvers variables fuel itemType selected resolved
            (path ++ [.index index]) [] [] false
        · intro head hh
          split
          · rename_i errors he
            apply runEnsures_pure
            simp [SeededItemsReconstructs, ItemsSuccess, he]
          · refine runEnsures_bind (SeededItemsReconstructs path (index + 1)
              (GraphQL.Execution.completeValueList schema resolvers variables fuel itemType (selected.map eraseField) rest)) _ _ _ ?_ ?_
            · exact completeStreamItems_seeded schema resolvers variables fuel itemType selected rest path (index + 1)
            · intro tail ht
              exact runEnsures_pure _ _ (seededItems_cons path index hh ht)
  termination_by (fuel, 2, sizeOf itemType, sizeOf values)
  decreasing_by
    all_goals subst_vars; simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right
    all_goals omega
end

/-- Root collection and execution reconstruct basic entries, using collection erasure
and the plan witness. -/
theorem executeRoot_seeded (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues) (fuel : Nat) (parentType : Name)
    (source : ResolverValue ObjectRef) (selections : List Selection)
    : RunEnsures
        (SeededReconstructs (fields []) (fieldCursors [])
          (GraphQL.Execution.executeCollectedFields schema resolvers variables fuel
            parentType source
            (GraphQL.Execution.collectFields schema variables parentType source
              (SelectionSet.eraseIncrementalDirectives selections))))
        (executeRootSelectionSetCore schema resolvers variables fuel parentType source
          selections) := by
  simp only [executeRootSelectionSetCore]
  refine runEnsures_bind (fun collection => eraseGroups collection.fields =
    GraphQL.Execution.collectFields schema variables parentType source
      (SelectionSet.eraseIncrementalDirectives selections)) _ _ _ ?_ ?_
  · exact collectFields_erase schema variables parentType source selections none
  · intro collection hc
    simpa only [hc] using executePlan_seeded schema resolvers variables fuel parentType source collection [] [] []

end GraphQL.IncrementalDelivery.Correctness.SourceReconstruction
