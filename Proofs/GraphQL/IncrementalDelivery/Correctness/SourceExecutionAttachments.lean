import Proofs.GraphQL.IncrementalDelivery.Correctness.SourceAttachmentAlgebra
import Proofs.GraphQL.IncrementalDelivery.Semantics.MixedListShape

/-! Actual mixed execution creates the object/list attachment roots used by its
cursor-seeded work. Ownership and attachment use the same source-slice offsets.
-/

namespace GraphQL.IncrementalDelivery.Correctness.SourceAttachments

open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Semantics
open Semantics.MixedPaths
open DeliveryPaths
open TypedResponse (Entry Atom)
open ResponsePositions (Cursors cursorAt listCursors fieldCursors itemCursors)

attribute [local simp] id_pure_eq id_bind_eq id_map_eq run_bind run_map

mutual
  /-- Executing a plan preserves owned attachment witnesses, by mutual execution
  induction and disjoint immediate/deferred field groups. -/
  theorem executePlan_attached (available : List Entry) (schema : Schema)
      (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
      (parentType : Name) (source : ResolverValue ObjectRef)
      (collection : FieldCollection) (hn : GroupsUnique collection.fields)
      (path : ResponsePath) (usages : List Nat) (deferMap : DeferMap)
      (ha : (path, Atom.object) ∈ available)
      : RunEnsures
          (OwnedAttachedCompletion available (TypedResponse.fields path)
            (fields true path) (fieldCursors path)
            (UnderFields path (collection.fields.map Prod.fst)))
          (executeExecutionPlan schema resolvers variables fuel parentType source
            collection.newDeferUsages (buildExecutionPlan collection.fields usages)
            path usages deferMap) := by
    let plan := buildExecutionPlan collection.fields usages
    have hperm := (buildExecutionPlan_perm collection.fields usages).map Prod.fst
    have hnames : (plan.collectedFieldsMap.map Prod.fst ++
        (plan.newCollectedFieldsMaps.flatMap Prod.snd).map Prod.fst).Nodup := by
      simpa [executionPlanGroups, plan] using hperm.nodup_iff.mpr hn
    have hwiden : ∀ p, UnderFields path (plan.collectedFieldsMap.map Prod.fst ++
        (plan.newCollectedFieldsMaps.flatMap Prod.snd).map Prod.fst) p →
        UnderFields path (collection.fields.map Prod.fst) p := by
      intro p
      apply underFields_mono
      intro name hm
      apply hperm.mem_iff.mp
      simpa [executionPlanGroups, plan] using hm
    simp only [executeExecutionPlan]
    refine runEnsures_bind
      (OwnedAttachedCompletion available (TypedResponse.fields path) (fields true path)
        (fieldCursors path) (UnderFields path (plan.collectedFieldsMap.map Prod.fst)))
      _ _ _ ?_ ?_
    · exact executeCollectedFields_attached available schema resolvers variables fuel parentType source _
        (List.nodup_append.mp hnames).1  path usages _
    · intro completed hc
      split
      · apply runEnsures_pure
        exact hc.mono (fun p hpc => hwiden p (underFields_mono
          (fun _ => List.mem_append_left _) hpc))
      · refine runEnsures_bind (OwnedAttachedWork available (UnderFields path
          ((plan.newCollectedFieldsMaps.flatMap Prod.snd).map Prod.fst))) _ _ _ ?_ ?_
        · exact collectExecutionGroups_attached available schema resolvers variables fuel parentType source _
            (List.nodup_append.mp hnames).2.1  path _ ha
        · intro work hw
          exact runEnsures_pure _ _ ((attached_combineWork_fields hnames hc hw).mono hwiden)
  termination_by (fuel, 6, 0, 0)
  decreasing_by
    all_goals simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right

  /-- Collected deferred groups attach to their ambient object, by induction through
  the groups and the deferred-completion attachment rule. -/
  theorem collectExecutionGroups_attached (available : List Entry) (schema : Schema)
      (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
      (parentType : Name) (source : ResolverValue ObjectRef)
      (partitions : List (List Nat × CollectedFieldsMap))
      (hn : GroupsUnique (partitions.flatMap Prod.snd)) (path : ResponsePath)
      (deferMap : DeferMap)
      (ha : (path, Atom.object) ∈ available)
      : RunEnsures
          (OwnedAttachedWork available
            (UnderFields path ((partitions.flatMap Prod.snd).map Prod.fst)))
          (collectExecutionGroups schema resolvers variables fuel parentType source
            partitions path deferMap) := by
    cases partitions with
    | nil =>
        simp only [collectExecutionGroups]
        exact runEnsures_pure _ _ ⟨⟨[], fun _ => .empty, owns_nil _⟩, [], fun _ => .empty, .empty⟩
    | cons partition rest =>
        rcases partition with ⟨usages, groups⟩
        have hnames : (groups.map Prod.fst ++ (rest.flatMap Prod.snd).map Prod.fst).Nodup := by
          simpa [GroupsUnique] using hn
        simp only [collectExecutionGroups, executeExecutionGroup]
        refine runEnsures_bind
          (OwnedAttachedCompletion available (TypedResponse.fields path)
            (fields true path) (fieldCursors path)
            (UnderFields path (groups.map Prod.fst)))
          _ _ _ ?_ ?_
        · exact executeCollectedFields_attached available schema resolvers variables fuel parentType source groups
            (List.nodup_append.mp hnames).1  path usages deferMap
        · intro completed hc
          refine runEnsures_bind (OwnedAttachedWork available
            (UnderFields path ((rest.flatMap Prod.snd).map Prod.fst))) _ _ _ ?_ ?_
          · exact collectExecutionGroups_attached available schema resolvers variables fuel parentType source rest
              (List.nodup_append.mp hnames).2.1  path deferMap ha
          · intro work hw
            apply runEnsures_pure
            simpa only [List.flatMap_cons, List.map_append]
              using attached_work_combine_fields hnames (hc.executionGroup _ ha) hw
  termination_by (fuel, 5, 0, sizeOf partitions)
  decreasing_by
    all_goals subst_vars; simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right
    all_goals omega

  /-- Collected fields preserve attachments, by field execution and disjoint key
  scopes.
  -/
  theorem executeCollectedFields_attached (available : List Entry) (schema : Schema)
      (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
      (parentType : Name) (source : ResolverValue ObjectRef) (groups : CollectedFieldsMap)
      (hn : GroupsUnique groups) (path : ResponsePath) (usages : List Nat)
      (deferMap : DeferMap)
      : RunEnsures
          (OwnedAttachedCompletion available (TypedResponse.fields path)
            (fields true path) (fieldCursors path)
            (UnderFields path (groups.map Prod.fst)))
          (executeCollectedFields schema resolvers variables fuel parentType source groups
            path usages deferMap) := by
    cases groups with
    | nil =>
        simp only [executeCollectedFields_nil]
        exact runEnsures_pure _ _ (attached_pure (owns_nil _))
    | cons group rest =>
        rcases group with ⟨name, selected⟩
        have hnames : (name :: rest.map Prod.fst).Nodup := hn
        simp only [executeCollectedFields_cons]
        refine runEnsures_bind
          (OwnedAttachedCompletion available (TypedResponse.fields path)
            (fields true path) (fieldCursors path) (Below (path ++ [.field name])))
          _ _ _ ?_ ?_
        · exact executeResponseField_attached available schema resolvers variables fuel parentType source name selected
             path usages deferMap
        · intro head hh
          refine runEnsures_bind (OwnedAttachedCompletion available (TypedResponse.fields path) (fields true path) (fieldCursors path)
            (UnderFields path (rest.map Prod.fst))) _ _ _ ?_ ?_
          · exact executeCollectedFields_attached available schema resolvers variables fuel parentType source rest
              (List.nodup_cons.mp hnames).2  path usages deferMap
          · intro tail ht
            exact runEnsures_pure _ _ (attached_combine_fields (leftNames := [name]) hnames
              (hh.mono (fun _ hp => ⟨name, by simp, hp⟩)) ht)
  termination_by (fuel, 4, 0, sizeOf groups)
  decreasing_by
    all_goals subst_vars; simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right
    all_goals omega

  /-- A response field preserves attachments, by value completion and field wrapping. -/
  theorem executeResponseField_attached (available : List Entry) (schema : Schema)
      (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
      (parentType : Name) (source : ResolverValue ObjectRef) (name : Name)
      (selected : List ExecutableField) (path : ResponsePath) (usages : List Nat)
      (deferMap : DeferMap)
      : RunEnsures
          (OwnedAttachedCompletion available (TypedResponse.fields path)
            (fields true path) (fieldCursors path) (Below (path ++ [.field name])))
          (executeResponseField schema resolvers variables fuel parentType source name
            selected path usages deferMap) := by
    cases fuel with
    | zero => simp [executeResponseField, RunEnsures, attached_error]
    | succ fuel =>
        cases selected with
        | nil => simp [executeResponseField, RunEnsures, attached_error]
        | cons field rest =>
            simp only [executeResponseField]
            split
            · exact runEnsures_pure _ _ (attached_error _ _ _ _ _ _)
            · split
              · exact runEnsures_pure _ _ (attached_failedField _ _ _ _)
              · split
                · exact runEnsures_pure _ _ (attached_failedField _ _ _ _)
                · refine runEnsures_bind (OwnedAttachedCompletion available (TypedResponse.value (path ++ [.field name])) (value true (path ++ [.field name])) (listCursors (path ++ [.field name])) (Below (path ++ [.field name]))) _ _ _ ?_ ?_
                  · exact completeValue_attached available schema resolvers variables fuel _ _ _
                      (path ++ [.field name]) usages deferMap true
                  · intro completed hc
                    exact runEnsures_pure _ _ (attached_map (fun _ => by simp [fields]) (fun _ => by simp [fieldCursors])
                      (fun _ => by simp [TypedResponse.fields]) hc)
  termination_by (fuel, 3, 0, sizeOf selected)
  decreasing_by
    all_goals subst_vars; simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right

  /-- Value completion supplies each container before its child work, by mutual
  induction over fuel, types, and resolver values. -/
  theorem completeValue_attached (available : List Entry) (schema : Schema)
      (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
      (fieldType : TypeRef) (selected : List ExecutableField)
      (resolved : ResolverValue ObjectRef) (path : ResponsePath) (usages : List Nat)
      (deferMap : DeferMap) (allowStream : Bool)
      : RunEnsures
          (OwnedAttachedCompletion available (TypedResponse.value path)
            (value true path) (listCursors path) (Below path))
          (completeValue schema resolvers variables fuel fieldType selected resolved path
            usages deferMap allowStream) := by
    cases fuel with
    | zero => simp [completeValue, RunEnsures, attached_error]
    | succ fuel =>
        cases fieldType with
        | nonNull inner =>
            simp only [completeValue]
            refine runEnsures_bind (OwnedAttachedCompletion available (TypedResponse.value path) (value true path) (listCursors path) (Below path)) _ _ _ ?_ ?_
            · exact completeValue_attached available schema resolvers variables (fuel + 1) inner selected resolved
                 path usages deferMap allowStream
            · intro completed hc
              exact runEnsures_pure _ _ (attached_nonNull hc)
        | named parentType =>
            cases resolved with
            | null =>
                simp only [completeValue]
                exact runEnsures_pure _ _ (attached_pure (owns_singleton (below_self _)))
            | scalar scalar =>
                simp only [completeValue]
                split
                · exact runEnsures_pure _ _ (attached_error _ _ _ _ _ _)
                · exact runEnsures_pure _ _ (attached_pure (owns_singleton (below_self _)))
            | list items => simp [completeValue, RunEnsures, attached_error]
            | object runtimeType ref =>
                simp only [completeValue]
                split
                · exact runEnsures_pure _ _ (attached_error _ _ _ _ _ _)
                · refine runEnsures_bind (fun collection => GroupsUnique collection.fields) _ _ _ ?_ ?_
                  · exact collectSubfields_unique schema variables runtimeType (.object runtimeType ref) selected
                  · intro collection hc
                    refine runEnsures_bind (OwnedAttachedCompletion (available ++ [(path, Atom.object)]) (TypedResponse.fields path) (fields true path) (fieldCursors path)
                      (UnderFields path (collection.fields.map Prod.fst))) _ _ _ ?_ ?_
                    · exact executePlan_attached (available ++ [(path, Atom.object)]) schema resolvers variables fuel runtimeType
                        (.object runtimeType ref) collection hc path usages deferMap (by simp)
                    · intro completed hv
                      exact runEnsures_pure _ _ (attached_catchNull (fun _ => rfl) (fun _ _ _ _ h => h) (fun _ => rfl) hv
                        (fun _ => underFields_below) (fun _ => underFields_ne))
        | list inner =>
            cases resolved with
            | null =>
                simp only [completeValue]
                exact runEnsures_pure _ _ (attached_pure (owns_singleton (below_self _)))
            | scalar scalar => simp [completeValue, RunEnsures, attached_error]
            | object runtimeType ref =>
                simp [completeValue, RunEnsures, attached_error]
            | list items =>
                simpa only [completeValue] using completeListValueWithStream_attached available schema resolvers variables fuel inner selected items
                   path usages deferMap allowStream
  termination_by (fuel, 1, sizeOf fieldType, 0)
  decreasing_by
    all_goals subst_vars; simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right

  /-- Stream-aware list completion attaches the suffix to its initial list, using
  ordinary prefix completion and the streamed-suffix attachment rule. -/
  theorem completeListValueWithStream_attached (available : List Entry) (schema : Schema)
      (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
      (inner : TypeRef) (selected : List ExecutableField)
      (values : List (ResolverValue ObjectRef)) (path : ResponsePath) (usages : List Nat)
      (deferMap : DeferMap) (allowStream : Bool)
      : RunEnsures
          (OwnedAttachedCompletion available (TypedResponse.value path)
            (value true path) (listCursors path) (Below path))
          (completeListValueWithStream schema resolvers variables fuel inner selected
            values path usages deferMap allowStream) := by
    unfold completeListValueWithStream
    dsimp only
    split
    · exact runEnsures_pure _ _ (attached_pure (owns_singleton (below_self _)))
    · refine runEnsures_bind (OwnedAttachedCompletion (available ++ [(path, Atom.list)]) (TypedResponse.items path 0) (items true path 0) (itemCursors path 0)
        (UnderItemRange path 0 values.length)) _ _ _ ?_ ?_
      · simpa only [Nat.zero_add] using completeListValue_attached (available ++ [(path, Atom.list)]) schema resolvers variables fuel inner selected values  path 0 usages deferMap
      · intro completed hc
        exact runEnsures_pure _ _ (attached_catchNull (fun _ => rfl) (cursorExtends_list_items path) (fun _ => rfl) hc
          (fun _ ⟨_, _, _, hb⟩ => below_child hb) (fun _ ⟨_, _, _, hb⟩ => below_child_ne hb))
    · rename_i usage _
      refine runEnsures_bind
        (fun initial =>
          OwnedAttachedCompletion (available ++ [(path, Atom.list)])
            (TypedResponse.items path 0) (items true path 0) (itemCursors path 0)
            (UnderItemRange path 0 (values.take usage.initialCount).length) initial
          ∧ ∀ data errors,
              initial.result = .ok (data, errors)
              → data.length = (values.take usage.initialCount).length)
        _ _ _ ?_ ?_
      · intro state
        refine ⟨?_, ?_⟩
        · simpa only [Nat.zero_add] using completeListValue_attached (available ++ [(path, Atom.list)]) schema resolvers variables fuel inner selected
            (values.take usage.initialCount) path 0 usages deferMap state
        · exact completeListValue_result_length schema resolvers variables fuel inner selected
            (values.take usage.initialCount) path 0 usages deferMap state
      · intro initial hi
        obtain ⟨hi, hlength⟩ := hi
        split
        · exact runEnsures_pure _ _ (attached_catchNull (fun _ => rfl) (cursorExtends_list_items path) (fun _ => rfl) hi
            (fun _ ⟨_, _, _, hb⟩ => below_child hb) (fun _ ⟨_, _, _, hb⟩ => below_child_ne hb))
        · rename_i data he
          split
          · exact runEnsures_pure _ _ (attached_catchNull (fun _ => rfl) (cursorExtends_list_items path) (fun _ => rfl) hi
              (fun _ ⟨_, _, _, hb⟩ => below_child hb) (fun _ ⟨_, _, _, hb⟩ => below_child_ne hb))
          · rename_i htail
            have hcount : usage.initialCount ≤ values.length := by omega
            have hlen : data.1.length = usage.initialCount := by
              simpa only [List.length_take, Nat.min_eq_left hcount]
                using hlength data.1 data.2 he
            refine runEnsures_bind (fun _ : Nat => True) _ _ _ (fun _ => trivial) ?_
            intro key _
            refine runEnsures_bind
              (OwnedAttachedItems (available ++ [(path, Atom.list)]) path
                usage.initialCount (UnderItems path usage.initialCount))
              _ _ _ ?_ ?_
            · exact completeStreamItems_attached (available ++ [(path, Atom.list)]) schema resolvers variables fuel inner _ _  path usage.initialCount
            · intro tail ht
              apply runEnsures_pure
              exact attached_streamPrefix hi he (by simp only [List.length_take]; omega) hlen rfl ht
  termination_by (fuel, 3, 0, 0)
  decreasing_by
    all_goals subst_vars; simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right

  /-- Ordinary list completion preserves attachments, by consecutive-index induction. -/
  theorem completeListValue_attached (available : List Entry) (schema : Schema)
      (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
      (itemType : TypeRef) (selected : List ExecutableField)
      (values : List (ResolverValue ObjectRef)) (path : ResponsePath) (index : Nat)
      (usages : List Nat) (deferMap : DeferMap)
      : RunEnsures
          (OwnedAttachedCompletion available (TypedResponse.items path index)
            (items true path index) (itemCursors path index)
            (UnderItemRange path index (index + values.length)))
          (completeListValue schema resolvers variables fuel itemType selected values path
            index usages deferMap) := by
    cases values with
    | nil =>
        simp only [completeListValue]
        exact runEnsures_pure _ _ (attached_pure (owns_nil _))
    | cons resolved rest =>
        simp only [completeListValue]
        refine runEnsures_bind
          (OwnedAttachedCompletion available
            (TypedResponse.value (path ++ [.index index]))
            (value true (path ++ [.index index])) (listCursors (path ++ [.index index]))
            (Below (path ++ [.index index])))
          _ _ _ ?_ ?_
        · exact completeValue_attached available schema resolvers variables fuel itemType selected resolved
             (path ++ [.index index]) usages deferMap false
        · intro head hh
          refine runEnsures_bind (OwnedAttachedCompletion available (TypedResponse.items path (index + 1)) (items true path (index + 1)) (itemCursors path (index + 1))
            (UnderItemRange path (index + 1) (index + 1 + rest.length))) _ _ _ ?_ ?_
          · exact completeListValue_attached available schema resolvers variables fuel itemType selected rest
               path (index + 1) usages deferMap
          · intro tail ht
            apply runEnsures_pure
            apply attached_combine (f := List.cons) (pc := items true path index)
              (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
              (listCursors_positions _) (itemCursors_positions _ _) hh ht
            · intro p hhead ⟨next, hn, _, hb⟩
              exact underItems_disjoint hhead ⟨next, hn, hb⟩
            · exact fun _ hp => ⟨index, Nat.le_refl _, by simp, hp⟩
            · intro p ⟨next, hn, hf, hp⟩
              exact ⟨next, by omega, by simp only [List.length_cons]; omega, hp⟩
  termination_by (fuel, 2, sizeOf itemType, sizeOf values)
  decreasing_by
    all_goals subst_vars; simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right
    all_goals omega

  /-- Stream item completion preserves indexed attachments, by combining the head's
  completion with the recursively attached suffix. -/
  theorem completeStreamItems_attached (available : List Entry) (schema : Schema)
      (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
      (itemType : TypeRef) (selected : List ExecutableField)
      (values : List (ResolverValue ObjectRef)) (path : ResponsePath) (index : Nat)
      : RunEnsures (OwnedAttachedItems available path index (UnderItems path index))
          (completeStreamItems schema resolvers variables fuel itemType selected values
            path index) := by
    cases values with
    | nil =>
        simp only [completeStreamItems]
        exact runEnsures_pure _ _ ⟨⟨[], .nil, owns_nil _⟩, [], .nil, .nil⟩
    | cons resolved rest =>
        simp only [completeStreamItems]
        refine runEnsures_bind
          (OwnedAttachedCompletion available
            (TypedResponse.value (path ++ [.index index]))
            (value true (path ++ [.index index])) (listCursors (path ++ [.index index]))
            (Below (path ++ [.index index])))
          _ _ _ ?_ ?_
        · exact completeValue_attached available schema resolvers variables fuel itemType selected resolved
             (path ++ [.index index]) [] [] false
        · intro head hh
          split
          · rename_i errors he
            apply runEnsures_pure
            have hs : ItemCursorSeed path index [(head.result, .empty)] [[]] := by
              simpa only [he, result, List.nil_append]
                using (ItemCursorSeed.cons (path := path) (index := index)
                        (completed := head.result) WorkCursorSeed.empty
                        ItemCursorSeed.nil)
            refine ⟨⟨[[]], hs, owns_nil _⟩, [[]], hs, ?_⟩
            simpa only [he, result, List.nil_append]
              using (ItemsAttached.cons (available := available) (path := path)
                      (index := index) (completed := head.result) WorkAttached.empty
                      ItemsAttached.nil)
          · refine runEnsures_bind (OwnedAttachedItems available path (index + 1)
              (UnderItems path (index + 1))) _ _ _ ?_ ?_
            · exact completeStreamItems_attached available schema resolvers variables fuel itemType selected rest
                 path (index + 1)
            · intro tail ht
              exact runEnsures_pure _ _ (attached_items_cons_underItems hh ht)
  termination_by (fuel, 2, sizeOf itemType, sizeOf values)
  decreasing_by
    all_goals subst_vars; simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right
    all_goals omega
end

/-- Root execution preserves attachments to the given ambient root object, by the
explicit root-plan equation and the execution-plan witness. -/
theorem executeRoot_attached_fields (available : List Entry) (schema : Schema)
    (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
    (parentType : Name) (source : ResolverValue ObjectRef) (selections : List Selection)
    (ha : ([], Atom.object) ∈ available)
    : RunEnsures
        (OwnedAttachedCompletion available (TypedResponse.fields []) (fields true [])
          (fieldCursors []) (fun path => path ≠ []))
        (executeRootSelectionSetCore schema resolvers variables fuel parentType source
          selections) := by
  simp only [executeRootSelectionSetCore]
  refine runEnsures_bind (fun collection => GroupsUnique collection.fields) _ _ _ ?_ ?_
  · exact collectFields_unique schema variables parentType source selections none
  · intro collection hc state
    exact (executePlan_attached available schema resolvers variables fuel parentType source collection hc
       [] [] [] ha state).mono (fun _ => underFields_ne)

/-- Root work has a shared seeded attachment witness with only the root object
assumed available, by specializing the root-field theorem. -/
theorem executeRoot_seeded_attached (schema : Schema)
    (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
    (parentType : Name) (source : ResolverValue ObjectRef) (selections : List Selection)
    : RunEnsures
        (OwnedAttachedCompletion [([], Atom.object)] (TypedResponse.fields [])
          (fields true []) (fieldCursors []) (fun path => path ≠ []))
        (executeRootSelectionSetCore schema resolvers variables fuel parentType source
          selections) :=
  executeRoot_attached_fields _ schema resolvers variables fuel parentType source
    selections (by simp)

end GraphQL.IncrementalDelivery.Correctness.SourceAttachments
