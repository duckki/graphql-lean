import Proofs.GraphQL.IncrementalDelivery.Semantics.MixedPathOwnership
import Proofs.GraphQL.IncrementalDelivery.Semantics.CollectedPaths

/-! Actual mixed execution owns disjoint absolute response positions. Stream item
indices are proof witnesses attached to the exact generated work, not a claim about
wire decoding or cursor reconstruction. Bounded ordinary-list ranges separate the
initial prefix from the streamed tail, including errors and discarded child work.
-/

namespace GraphQL.IncrementalDelivery.Semantics.MixedPaths

open GraphQL.IncrementalDelivery.Execution
open DeliveryPaths

attribute [local simp] id_pure_eq id_bind_eq id_map_eq run_bind run_map

theorem ownsItems_cons_underItems {containers : Bool} {path : ResponsePath} {index : Nat}
    {head : Completion ResponseValue} {tail : List (Result ResponseValue × Work)}
    (hh
      : OwnsCompletion containers (value containers (path ++ [.index index]))
          (Below (path ++ [.index index])) head)
    (ht : OwnsItems containers path (index + 1) (UnderItems path (index + 1)) tail)
    : OwnsItems containers path index (UnderItems path index)
        ((head.result, head.work) :: tail) := by
  apply ownsItems_cons hh ht
  · exact fun _ => underItems_disjoint
  · exact fun _ hp => ⟨index, Nat.le_refl _, hp⟩
  · intro p hp
    obtain ⟨next, hn, hp⟩ := hp
    exact ⟨next, by omega, hp⟩

theorem ownsCompletion_streamPrefix {containers : Bool} {path : ResponsePath}
    {finish start : Nat} {initial : Completion (List ResponseValue)}
    {data : List ResponseValue} {errors : Nat} {node : DeliveryNode}
    {items : List (Result ResponseValue × Work)}
    (hi
      : OwnsCompletion containers (DeliveryPaths.items containers path 0)
          (UnderItemRange path 0 finish) initial)
    (he : initial.result = .ok (data, errors)) (hb : finish ≤ start)
    (hp : node.path = path)
    (ht : OwnsItems containers path start (UnderItems path start) items)
    : OwnsCompletion containers (value containers path) (Below path)
        {
          initial.catchNull ResponseValue.list with
            work :=
              .combine (initial.catchNull ResponseValue.list).work (.stream node items)
        } := by
  have hprefix : OwnsCompletion containers (value containers path)
      (fun p => p = path ∨ UnderItemRange path 0 finish p)
      (initial.catchNull ResponseValue.list) := by
    obtain ⟨s, hs, ho⟩ := hi
    refine ⟨s, by simpa only [Completion.catchNull, he] using hs, ?_⟩
    simp only [he, result] at ho
    simp only [Completion.catchNull, he, result, value, List.append_assoc]
    cases containers with
    | false => simpa using ho.mono (fun _ => Or.inr)
    | true =>
        apply owns_append (owns_singleton (rfl : path = path)) ho
        · intro p hp hrange
          have hn : p ≠ path := by
            obtain ⟨index, _, _, hbelow⟩ := hrange
            exact below_child_ne hbelow
          exact hn hp.symm
        · exact fun _ hp => Or.inl hp.symm
        · exact fun _ => Or.inr
  have hstream : OwnsWork containers (UnderItems path start) (.stream node items) := by
    obtain ⟨s, hs, ho⟩ := ht
    refine ⟨s, .stream (index := start) ?_, ho⟩
    simpa only [hp] using hs
  apply ownsCompletion_combineWork hprefix hstream
  · intro p hprefix htail
    rcases hprefix with hroot | hrange
    · exact underItems_ne htail hroot
    · obtain ⟨left, _, hl, hleft⟩ := hrange
      obtain ⟨right, hr, hright⟩ := htail
      have heq := below_children_eq hleft hright
      cases heq
      omega
  · intro p hprefix
    rcases hprefix with hroot | ⟨index, _, _, hbelow⟩
    · subst p; exact below_self _
    · exact below_child hbelow
  · exact fun _ => underItems_below

mutual
  theorem executePlan_owns (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variables : VariableValues) (fuel : Nat) (parentType : Name)
      (source : ResolverValue ObjectRef) (collection : FieldCollection)
      (hn : GroupsUnique collection.fields) (containers : Bool) (path : ResponsePath)
      (usages : List Nat) (deferMap : DeferMap)
      : RunEnsures
          (OwnsCompletion containers (fields containers path)
            (UnderFields path (collection.fields.map Prod.fst)))
          (executeExecutionPlan schema resolvers variables fuel parentType source
            collection.newDeferUsages (buildExecutionPlan collection.fields usages) path
            usages deferMap) := by
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
    refine runEnsures_bind (OwnsCompletion containers (fields containers path)
      (UnderFields path (plan.collectedFieldsMap.map Prod.fst))) _ _ _ ?_ ?_
    · exact executeCollectedFields_owns schema resolvers variables fuel parentType source _
        (List.nodup_append.mp hnames).1 containers path usages _
    · intro completed hc
      split
      · apply runEnsures_pure
        exact hc.mono (fun p hpc => hwiden p (underFields_mono
          (fun _ => List.mem_append_left _) hpc))
      · refine runEnsures_bind (OwnsWork containers (UnderFields path
          ((plan.newCollectedFieldsMaps.flatMap Prod.snd).map Prod.fst))) _ _ _ ?_ ?_
        · exact collectExecutionGroups_owns schema resolvers variables fuel parentType source _
            (List.nodup_append.mp hnames).2.1 containers path _
        · intro work hw
          exact runEnsures_pure _ _
            ((ownsCompletion_combineWork_fields hnames hc hw).mono hwiden)
  termination_by (fuel, 6, 0, 0)
  decreasing_by
    all_goals simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right

  theorem collectExecutionGroups_owns (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variables : VariableValues) (fuel : Nat) (parentType : Name)
      (source : ResolverValue ObjectRef)
      (partitions : List (List Nat × CollectedFieldsMap))
      (hn : GroupsUnique (partitions.flatMap Prod.snd)) (containers : Bool)
      (path : ResponsePath) (deferMap : DeferMap)
      : RunEnsures
          (OwnsWork containers
            (UnderFields path ((partitions.flatMap Prod.snd).map Prod.fst)))
          (collectExecutionGroups schema resolvers variables fuel parentType source
            partitions path deferMap) := by
    cases partitions with
    | nil =>
        simp only [collectExecutionGroups]
        exact runEnsures_pure _ _ ⟨[], .empty, owns_nil _⟩
    | cons partition rest =>
        rcases partition with ⟨usages, groups⟩
        have hnames : (groups.map Prod.fst ++ (rest.flatMap Prod.snd).map Prod.fst).Nodup := by
          simpa [GroupsUnique] using hn
        simp only [collectExecutionGroups, executeExecutionGroup]
        refine runEnsures_bind (OwnsCompletion containers (fields containers path)
          (UnderFields path (groups.map Prod.fst))) _ _ _ ?_ ?_
        · exact executeCollectedFields_owns schema resolvers variables fuel parentType source groups
            (List.nodup_append.mp hnames).1 containers path usages deferMap
        · intro completed hc
          refine runEnsures_bind (OwnsWork containers
            (UnderFields path ((rest.flatMap Prod.snd).map Prod.fst))) _ _ _ ?_ ?_
          · exact collectExecutionGroups_owns schema resolvers variables fuel parentType source rest
              (List.nodup_append.mp hnames).2.1 containers path deferMap
          · intro work hw
            apply runEnsures_pure
            simpa only [List.flatMap_cons, List.map_append]
              using ownsWork_combine_fields hnames (hc.executionGroup _) hw
  termination_by (fuel, 5, 0, sizeOf partitions)
  decreasing_by
    all_goals subst_vars; simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right
    all_goals omega

  theorem executeCollectedFields_owns (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variables : VariableValues) (fuel : Nat) (parentType : Name)
      (source : ResolverValue ObjectRef) (groups : CollectedFieldsMap)
      (hn : GroupsUnique groups) (containers : Bool) (path : ResponsePath)
      (usages : List Nat) (deferMap : DeferMap)
      : RunEnsures
          (OwnsCompletion containers (fields containers path)
            (UnderFields path (groups.map Prod.fst)))
          (executeCollectedFields schema resolvers variables fuel parentType source groups
            path usages deferMap) := by
    cases groups with
    | nil =>
        simp only [executeCollectedFields_nil]
        exact runEnsures_pure _ _ (ownsCompletion_pure (owns_nil _))
    | cons group rest =>
        rcases group with ⟨name, selected⟩
        have hnames : (name :: rest.map Prod.fst).Nodup := hn
        simp only [executeCollectedFields_cons]
        refine runEnsures_bind (OwnsCompletion containers (fields containers path)
          (Below (path ++ [.field name]))) _ _ _ ?_ ?_
        · exact executeResponseField_owns schema resolvers variables fuel parentType
            source name selected
            containers path usages deferMap
        · intro head hh
          refine runEnsures_bind (OwnsCompletion containers (fields containers path)
            (UnderFields path (rest.map Prod.fst))) _ _ _ ?_ ?_
          · exact executeCollectedFields_owns schema resolvers variables fuel parentType source rest
              (List.nodup_cons.mp hnames).2 containers path usages deferMap
          · intro tail ht
            exact runEnsures_pure _ _ (ownsCompletion_combine_fields (leftNames := [name]) hnames
              (hh.mono (fun _ hp => ⟨name, by simp, hp⟩)) ht)
  termination_by (fuel, 4, 0, sizeOf groups)
  decreasing_by
    all_goals subst_vars; simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right
    all_goals omega

  theorem executeResponseField_owns (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variables : VariableValues) (fuel : Nat) (parentType : Name)
      (source : ResolverValue ObjectRef) (name : Name) (selected : List ExecutableField)
      (containers : Bool) (path : ResponsePath) (usages : List Nat) (deferMap : DeferMap)
      : RunEnsures
          (OwnsCompletion containers (fields containers path)
            (Below (path ++ [.field name])))
          (executeResponseField schema resolvers variables fuel parentType source name
            selected path usages deferMap) := by
    cases fuel with
    | zero => simp [executeResponseField, RunEnsures, ownsCompletion_error]
    | succ fuel =>
        cases selected with
        | nil => simp [executeResponseField, RunEnsures, ownsCompletion_error]
        | cons field rest =>
            simp only [executeResponseField]
            split
            · exact runEnsures_pure _ _ (ownsCompletion_error _ _ _ _)
            · split
              · exact runEnsures_pure _ _ (ownsCompletion_failedField _ _ _ _)
              · split
                · exact runEnsures_pure _ _ (ownsCompletion_failedField _ _ _ _)
                · refine runEnsures_bind (OwnsCompletion containers
                    (value containers (path ++ [.field name])) (Below (path ++ [.field name]))) _ _ _ ?_ ?_
                  · exact completeValue_owns schema resolvers variables fuel _ _ _ containers
                      (path ++ [.field name]) usages deferMap true
                  · intro completed hc
                    exact runEnsures_pure _ _ (ownsCompletion_map (fun _ => by simp [fields]) hc)
  termination_by (fuel, 3, 0, sizeOf selected)
  decreasing_by
    all_goals subst_vars; simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right

  theorem completeValue_owns (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variables : VariableValues) (fuel : Nat) (fieldType : TypeRef)
      (selected : List ExecutableField) (resolved : ResolverValue ObjectRef)
      (containers : Bool) (path : ResponsePath) (usages : List Nat) (deferMap : DeferMap)
      (allowStream : Bool)
      : RunEnsures (OwnsCompletion containers (value containers path) (Below path))
          (completeValue schema resolvers variables fuel fieldType selected resolved path
            usages deferMap allowStream) := by
    cases fuel with
    | zero => simp [completeValue, RunEnsures, ownsCompletion_error]
    | succ fuel =>
        cases fieldType with
        | nonNull inner =>
            simp only [completeValue]
            refine runEnsures_bind (OwnsCompletion containers (value containers path) (Below path)) _ _ _ ?_ ?_
            · exact completeValue_owns schema resolvers variables (fuel + 1) inner selected resolved
                containers path usages deferMap allowStream
            · intro completed hc
              exact runEnsures_pure _ _ (ownsCompletion_nonNull hc)
        | named parentType =>
            cases resolved with
            | null =>
                simp only [completeValue]
                exact runEnsures_pure _ _ (ownsCompletion_pure (owns_singleton (below_self _)))
            | scalar scalar =>
                simp only [completeValue]
                split
                · exact runEnsures_pure _ _ (ownsCompletion_error _ _ _ _)
                · exact runEnsures_pure _ _ (ownsCompletion_pure (owns_singleton (below_self _)))
            | list items => simp [completeValue, RunEnsures, ownsCompletion_error]
            | object runtimeType ref =>
                simp only [completeValue]
                split
                · exact runEnsures_pure _ _ (ownsCompletion_error _ _ _ _)
                · refine runEnsures_bind (fun collection => GroupsUnique collection.fields) _ _ _ ?_ ?_
                  · exact collectSubfields_unique schema variables runtimeType (.object runtimeType ref) selected
                  · intro collection hc
                    refine runEnsures_bind (OwnsCompletion containers (fields containers path)
                      (UnderFields path (collection.fields.map Prod.fst))) _ _ _ ?_ ?_
                    · exact executePlan_owns schema resolvers variables fuel runtimeType
                        (.object runtimeType ref) collection hc containers path usages deferMap
                    · intro completed hv
                      exact runEnsures_pure _ _ (ownsCompletion_catchNull (fun _ => rfl) hv
                        (fun _ => underFields_below) (fun _ => underFields_ne))
        | list inner =>
            cases resolved with
            | null =>
                simp only [completeValue]
                exact runEnsures_pure _ _ (ownsCompletion_pure (owns_singleton (below_self _)))
            | scalar scalar => simp [completeValue, RunEnsures, ownsCompletion_error]
            | object runtimeType ref =>
                simp [completeValue, RunEnsures, ownsCompletion_error]
            | list items =>
                simpa only [completeValue] using completeListValueWithStream_owns schema
                  resolvers variables fuel inner selected items
                  containers path usages deferMap allowStream
  termination_by (fuel, 1, sizeOf fieldType, 0)
  decreasing_by
    all_goals subst_vars; simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right

  theorem completeListValueWithStream_owns (schema : Schema)
      (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
      (inner : TypeRef) (selected : List ExecutableField)
      (values : List (ResolverValue ObjectRef)) (containers : Bool) (path : ResponsePath)
      (usages : List Nat) (deferMap : DeferMap) (allowStream : Bool)
      : RunEnsures (OwnsCompletion containers (value containers path) (Below path))
          (completeListValueWithStream schema resolvers variables fuel inner selected
            values path usages deferMap allowStream) := by
    unfold completeListValueWithStream
    dsimp only
    split
    · exact runEnsures_pure _ _ (ownsCompletion_pure (owns_singleton (below_self _)))
    · refine runEnsures_bind (OwnsCompletion containers (items containers path 0)
        (UnderItemRange path 0 values.length)) _ _ _ ?_ ?_
      · simpa only [Nat.zero_add] using completeListValue_owns schema resolvers variables
          fuel inner selected values containers path 0 usages deferMap
      · intro completed hc
        exact runEnsures_pure _ _ (ownsCompletion_catchNull (fun _ => rfl) hc
          (fun _ ⟨_, _, _, hb⟩ => below_child hb) (fun _ ⟨_, _, _, hb⟩ => below_child_ne hb))
    · rename_i usage _
      refine runEnsures_bind (OwnsCompletion containers (items containers path 0)
        (UnderItemRange path 0 (values.take usage.initialCount).length)) _ _ _ ?_ ?_
      · simpa only [Nat.zero_add] using completeListValue_owns schema resolvers variables
          fuel inner selected
          (values.take usage.initialCount) containers path 0 usages deferMap
      · intro initial hi
        split
        · exact runEnsures_pure _ _ (ownsCompletion_catchNull (fun _ => rfl) hi
            (fun _ ⟨_, _, _, hb⟩ => below_child hb) (fun _ ⟨_, _, _, hb⟩ => below_child_ne hb))
        · rename_i data he
          split
          · exact runEnsures_pure _ _ (ownsCompletion_catchNull (fun _ => rfl) hi
              (fun _ ⟨_, _, _, hb⟩ => below_child hb) (fun _ ⟨_, _, _, hb⟩ => below_child_ne hb))
          · refine runEnsures_bind (fun _ : Nat => True) _ _ _ (fun _ => trivial) ?_
            intro key _
            refine runEnsures_bind (OwnsItems containers path usage.initialCount
              (UnderItems path usage.initialCount)) _ _ _ ?_ ?_
            · exact completeStreamItems_owns schema resolvers variables fuel inner _ _ containers path usage.initialCount
            · intro tail ht
              apply runEnsures_pure
              exact ownsCompletion_streamPrefix hi he (by simp only [List.length_take]; omega) rfl ht
  termination_by (fuel, 3, 0, 0)
  decreasing_by
    all_goals subst_vars; simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right

  theorem completeListValue_owns (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variables : VariableValues) (fuel : Nat) (itemType : TypeRef)
      (selected : List ExecutableField) (values : List (ResolverValue ObjectRef))
      (containers : Bool) (path : ResponsePath) (index : Nat) (usages : List Nat)
      (deferMap : DeferMap)
      : RunEnsures
          (OwnsCompletion containers (items containers path index)
            (UnderItemRange path index (index + values.length)))
          (completeListValue schema resolvers variables fuel itemType selected values path
            index usages deferMap) := by
    cases values with
    | nil =>
        simp only [completeListValue]
        exact runEnsures_pure _ _ (ownsCompletion_pure (owns_nil _))
    | cons resolved rest =>
        simp only [completeListValue]
        refine runEnsures_bind
          (OwnsCompletion containers (value containers (path ++ [.index index]))
            (Below (path ++ [.index index])))
          _ _ _ ?_ ?_
        · exact completeValue_owns schema resolvers variables fuel itemType selected resolved
            containers (path ++ [.index index]) usages deferMap false
        · intro head hh
          refine runEnsures_bind (OwnsCompletion containers (items containers path (index + 1))
            (UnderItemRange path (index + 1) (index + 1 + rest.length))) _ _ _ ?_ ?_
          · exact completeListValue_owns schema resolvers variables fuel itemType selected rest
              containers path (index + 1) usages deferMap
          · intro tail ht
            apply runEnsures_pure
            apply ownsCompletion_combine (f := List.cons) (pc := items containers path index)
              (fun _ _ => rfl) hh ht
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

  theorem completeStreamItems_owns (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variables : VariableValues) (fuel : Nat) (itemType : TypeRef)
      (selected : List ExecutableField) (values : List (ResolverValue ObjectRef))
      (containers : Bool) (path : ResponsePath) (index : Nat)
      : RunEnsures (OwnsItems containers path index (UnderItems path index))
          (completeStreamItems schema resolvers variables fuel itemType selected values
            path index) := by
    cases values with
    | nil =>
        simp only [completeStreamItems]
        exact runEnsures_pure _ _ ⟨[], .nil, owns_nil _⟩
    | cons resolved rest =>
        simp only [completeStreamItems]
        refine runEnsures_bind
          (OwnsCompletion containers (value containers (path ++ [.index index]))
            (Below (path ++ [.index index])))
          _ _ _ ?_ ?_
        · exact completeValue_owns schema resolvers variables fuel itemType selected resolved
            containers (path ++ [.index index]) [] [] false
        · intro head hh
          split
          · rename_i errors he
            apply runEnsures_pure
            exact ⟨[[]], by simpa only [he, result, List.nil_append] using
              (ItemSlices.cons (containers := containers) (path := path) (index := index)
                (completed := head.result) WorkSlices.empty ItemSlices.nil), owns_nil _⟩
          · refine runEnsures_bind (OwnsItems containers path (index + 1)
              (UnderItems path (index + 1))) _ _ _ ?_ ?_
            · exact completeStreamItems_owns schema resolvers variables fuel itemType selected rest
                containers path (index + 1)
            · intro tail ht
              exact runEnsures_pure _ _ (ownsItems_cons_underItems hh ht)
  termination_by (fuel, 2, sizeOf itemType, sizeOf values)
  decreasing_by
    all_goals subst_vars; simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right
    all_goals omega
end

theorem executeRoot_owns_fields (schema : Schema)
    (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
    (parentType : Name) (source : ResolverValue ObjectRef) (selections : List Selection)
    (containers : Bool)
    : RunEnsures
        (OwnsCompletion containers (fields containers []) (fun path => path ≠ []))
        (executeRootSelectionSetCore schema resolvers variables fuel parentType source
          selections) := by
  simp only [executeRootSelectionSetCore]
  refine runEnsures_bind (fun collection => GroupsUnique collection.fields) _ _ _ ?_ ?_
  · exact collectFields_unique schema variables parentType source selections none
  · intro collection hc state
    exact (executePlan_owns schema resolvers variables fuel parentType source collection hc
      containers [] [] [] state).mono (fun _ => underFields_ne)

end GraphQL.IncrementalDelivery.Semantics.MixedPaths
