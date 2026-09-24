import Proofs.GraphQL.IncrementalDelivery.Semantics.ContextCollection
import Proofs.GraphQL.IncrementalDelivery.Semantics.Completion

/-! Ordinary value completion agrees with basic execution inside an active defer group. -/

namespace GraphQL.IncrementalDelivery.Semantics

open GraphQL.IncrementalDelivery.Execution

attribute [local simp] id_pure_eq id_bind_eq id_map_eq run_bind run_map

variable {ObjectRef : Type}

theorem runMatches_after_contextCollection (usage : Option DeferUsage)
    (action : StateM Nat FieldCollection)
    (groups : List (Name × List GraphQL.Execution.ExecutableField))
    (next : FieldCollection → StateM Nat (Completion α)) (basic : Result α) (state : Nat)
    (h : CollectionInContext usage state (action.run state))
    (he : eraseGroups (action.run state).1.fields = groups)
    (hn
      : ∀ collection,
          collection.newDeferUsages = []
          → GroupsInContext usage collection.fields
          → eraseGroups collection.fields = groups
          → RunMatches (next collection) basic state)
    : RunMatches (action >>= next) basic state := by
  generalize hout : action.run state = output at h he
  rcases output with ⟨collection, final⟩
  rcases h with ⟨hstate, hnw, hp⟩
  dsimp only at hstate he
  subst final
  simpa [RunMatches, hout] using hn collection hnw hp he

theorem executePlan_inContext (usage : Option DeferUsage)
    (hvalid : ContextWellFormed usage) (deferMap : DeferMap)
    (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues) (fuel : Nat) (parentType : Name)
    (source : ResolverValue ObjectRef)
    (collection : FieldCollection) (path : ResponsePath) (state : Nat) (basic : Result _)
    (hn : collection.newDeferUsages = []) (hp : GroupsInContext usage collection.fields)
    (hr
      : RunMatches
          (executeCollectedFields schema resolvers variables fuel parentType source
            collection.fields path (contextKeys usage) deferMap) basic state)
    : RunMatches
        (executeExecutionPlan schema resolvers variables fuel parentType source
          collection.newDeferUsages
          (buildExecutionPlan collection.fields (contextKeys usage)) path
          (contextKeys usage) deferMap) basic state := by
  simp only [executeExecutionPlan, hn, getNewDeferMap, List.foldl_nil,
    buildExecutionPlan_inContext usage hvalid collection.fields hp]
  apply runMatches_bind _ _ _ _ _ hr
  intro completed hc
  cases he : completed.result with
  | error errors => simpa [he] using runMatches_pure completed basic state hc
  | ok result =>
      simp only [collectExecutionGroups]
      apply runMatches_pure
      exact ⟨by simpa [he] using hc.1, by simpa [Work.size] using hc.2⟩

theorem streamUsage_inContext (usage : Option DeferUsage) (variables : VariableValues)
    (fields : List ExecutableField) (h : FieldsInContext usage fields)
    : getStreamUsage variables (fields.head?.map ExecutableField.directives |>.getD [])
      = .ok none := by
  cases fields with
  | nil => rfl
  | cons field rest =>
      exact (directives_plain variables field.directives (h field (by simp)).2.1).2.2

mutual
  theorem executeCollectedFields_inContext (usage : Option DeferUsage)
      (hvalid : ContextWellFormed usage) (deferMap : DeferMap) (schema : Schema)
      (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
      (parentType : Name) (source : ResolverValue ObjectRef) (groups : CollectedFieldsMap)
      (hplain : GroupsInContext usage groups) (path : ResponsePath) (state : Nat)
      : RunMatches
          (executeCollectedFields schema resolvers variables fuel parentType source groups
            path (contextKeys usage) deferMap)
          (GraphQL.Execution.executeCollectedFields schema resolvers variables fuel
            parentType source (eraseGroups groups))
          state := by
    cases groups with
    | nil =>
        simp [executeCollectedFields_nil, GraphQL.Execution.executeCollectedFields,
        eraseGroups, RunMatches, CompletionMatches, Completion.pure, Work.size]
    | cons group rest =>
        rcases group with ⟨name, fields⟩
        have hf : FieldsInContext usage fields := (hplain (name, fields) (by simp)).2
        have hr : GroupsInContext usage rest := fun g h => hplain g (by simp [h])
        simp only [executeCollectedFields_cons, eraseGroups, List.map_cons, eraseGroup,
          GraphQL.Execution.executeCollectedFields]
        apply runMatches_bind _ _ _ _ _
          (executeResponseField_inContext usage hvalid deferMap schema resolvers variables
            fuel parentType
            source name fields hf path state)
        intro head hh
        apply runMatches_bind _ _ _ _ _
          (executeCollectedFields_inContext usage hvalid deferMap schema resolvers
            variables fuel parentType source rest hr path state)
        intro tail ht
        apply runMatches_pure
        exact completionMatches_combine List.append head tail _ _ hh ht
  termination_by (fuel, 4, 0, sizeOf groups)
  decreasing_by
    all_goals
      subst_vars
      simp_wf
      repeat first
        | apply Prod.Lex.left; omega
        | apply Prod.Lex.right
      try omega

  theorem executeResponseField_inContext (usage : Option DeferUsage)
      (hvalid : ContextWellFormed usage) (deferMap : DeferMap) (schema : Schema)
      (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
      (parentType : Name) (source : ResolverValue ObjectRef) (name : Name)
      (fields : List ExecutableField)
      (hplain : FieldsInContext usage fields) (path : ResponsePath) (state : Nat)
      : RunMatches
          (executeResponseField schema resolvers variables fuel parentType source name
            fields path (contextKeys usage) deferMap)
          (GraphQL.Execution.executeField schema resolvers variables fuel parentType
            source name (fields.map eraseField))
          state := by
    cases fields with
    | nil => cases fuel <;> simp [executeResponseField, GraphQL.Execution.executeField,
        RunMatches, CompletionMatches, Completion.error, Work.size]
    | cons field rest =>
        cases fuel with
        | zero => simp [executeResponseField, GraphQL.Execution.executeField,
          RunMatches, CompletionMatches, Completion.error, Work.size,
          GraphQL.Execution.outOfFuel]
        | succ fuel =>
            cases hf : schema.lookupField parentType field.fieldName with
            | none =>
                simp [executeResponseField, GraphQL.Execution.executeField, eraseField,
              hf, RunMatches, CompletionMatches, Completion.error, Work.size]
            | some definition =>
                cases ha
                      : coerceArgumentValues schema variables definition.arguments
                          field.arguments with
                | error =>
                    simp [executeResponseField, GraphQL.Execution.executeField, eraseField,
                  hf, ha, RunMatches, CompletionMatches, Work.size]
                | success arguments =>
                    cases hv
                          : resolveFieldValue resolvers parentType field.fieldName
                              arguments source with
                    | none =>
                        simp [executeResponseField, GraphQL.Execution.executeField, eraseField,
                      hf, ha, hv, RunMatches, CompletionMatches, Work.size]
                    | some value =>
                        simp only [executeResponseField, List.map_cons,
                          GraphQL.Execution.executeField,
                          eraseField, hf, ha, hv]
                        apply runMatches_bind _ _ _ _ _
                          (completeValue_inContext usage hvalid deferMap schema resolvers
                            variables fuel definition.outputType
                            (field :: rest) value hplain
                            (path ++ [ResponsePathSegment.field name]) true state)
                        intro completed hc
                        apply runMatches_pure
                        exact completionMatches_field name completed _ hc
  termination_by (fuel, 3, 0, sizeOf fields)
  decreasing_by
    all_goals
      subst_vars
      simp_wf
      repeat first
        | apply Prod.Lex.left; omega
        | apply Prod.Lex.right
      try omega

  theorem completeValue_inContext (usage : Option DeferUsage)
      (hvalid : ContextWellFormed usage) (deferMap : DeferMap) (schema : Schema)
      (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
      (fieldType : TypeRef) (fields : List ExecutableField)
      (value : ResolverValue ObjectRef) (hplain : FieldsInContext usage fields)
      (path : ResponsePath) (allowStream : Bool) (state : Nat)
      : RunMatches
          (completeValue schema resolvers variables fuel fieldType fields value path
            (contextKeys usage) deferMap allowStream)
          (GraphQL.Execution.completeValue schema resolvers variables fuel fieldType
            (fields.map eraseField) value)
          state := by
    cases fuel with
    | zero =>
        simp [completeValue, GraphQL.Execution.completeValue, RunMatches,
        CompletionMatches, Completion.error, Work.size, GraphQL.Execution.outOfFuel]
    | succ fuel =>
        cases fieldType with
        | nonNull inner =>
            simp only [completeValue, GraphQL.Execution.completeValue]
            apply runMatches_bind _ _ _ _ _
              (completeValue_inContext usage hvalid deferMap schema resolvers variables (fuel + 1)
                inner fields value hplain
                path allowStream state)
            intro completed hc
            apply runMatches_pure
            exact completionMatches_nonNull completed _ hc
        | named parentType =>
            cases value with
            | null => simp [completeValue, GraphQL.Execution.completeValue, RunMatches,
              CompletionMatches, Completion.pure, Work.size]
            | scalar scalar =>
                cases hc : (TypeRef.named parentType).isCompositeBool schema <;>
                  simp [completeValue, GraphQL.Execution.completeValue, hc, RunMatches,
                    CompletionMatches, Completion.pure, Completion.error, Work.size]
            | list items =>
                simp [completeValue, GraphQL.Execution.completeValue, RunMatches,
              CompletionMatches, Completion.error, Work.size]
            | object runtimeType ref =>
                cases hi : schema.typeIncludesObjectBool parentType runtimeType
                · simp [completeValue, GraphQL.Execution.completeValue, hi, RunMatches,
                    CompletionMatches, Completion.error, Work.size]
                · simp only [completeValue, GraphQL.Execution.completeValue, hi, Bool.not_true,
                    Bool.false_eq_true, ↓reduceIte]
                  apply runMatches_after_contextCollection usage _ _ _ _ _
                    (collectSubfields_inContext schema variables runtimeType (.object runtimeType
                      ref)
                      fields usage hplain state)
                    (collectSubfields_erase schema variables runtimeType (.object runtimeType ref)
                      fields state)
                  intro collection hn hp he
                  apply runMatches_bind _ _ _ _ _
                    (executePlan_inContext usage hvalid deferMap schema resolvers variables fuel
                      runtimeType (.object runtimeType ref)
                      collection path state _ hn hp
                      (executeCollectedFields_inContext usage hvalid deferMap schema resolvers
                        variables fuel runtimeType (.object runtimeType ref) collection.fields hp
                        path state))
                  intro completed hc
                  apply runMatches_pure
                  simpa [he] using completionMatches_catchNull ResponseValue.object completed _ hc
        | list inner =>
            cases value with
            | null => simp [completeValue, GraphQL.Execution.completeValue, RunMatches,
              CompletionMatches, Completion.pure, Work.size]
            | scalar scalar =>
                simp [completeValue, GraphQL.Execution.completeValue, RunMatches,
              CompletionMatches, Completion.error, Work.size]
            | object runtimeType ref =>
                simp [completeValue, GraphQL.Execution.completeValue, RunMatches,
            CompletionMatches, Completion.error, Work.size]
            | list items =>
                simp only [completeValue, GraphQL.Execution.completeValue,
                  completeListValueWithStream]
                have hs := streamUsage_inContext usage variables fields hplain
                have hs' : (if allowStream then
                    getStreamUsage variables
                      (fields.head?.map ExecutableField.directives |>.getD [])
                    else .ok none) = .ok none := by simp [hs]
                simp only [hs']
                apply runMatches_bind _ _ _ _ _
                  (completeListValue_inContext usage hvalid deferMap schema resolvers
                    variables fuel inner fields items hplain path 0 state)
                intro completed hc
                apply runMatches_pure
                exact completionMatches_catchNull ResponseValue.list completed _ hc
  termination_by (fuel, 1, sizeOf fieldType, 0)
  decreasing_by
    all_goals
      subst_vars
      simp_wf
      repeat first
        | apply Prod.Lex.left; omega
        | apply Prod.Lex.right
      try omega

  theorem completeListValue_inContext (usage : Option DeferUsage)
      (hvalid : ContextWellFormed usage) (deferMap : DeferMap) (schema : Schema)
      (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
      (itemType : TypeRef) (fields : List ExecutableField)
      (values : List (ResolverValue ObjectRef)) (hplain : FieldsInContext usage fields)
      (path : ResponsePath) (index state : Nat)
      : RunMatches
          (completeListValue schema resolvers variables fuel itemType fields values
            path index (contextKeys usage) deferMap)
          (GraphQL.Execution.completeValueList schema resolvers variables fuel itemType
            (fields.map eraseField) values)
          state := by
    cases values with
    | nil => simp [completeListValue, GraphQL.Execution.completeValueList, RunMatches,
        CompletionMatches, Completion.pure, Work.size]
    | cons value rest =>
        simp only [completeListValue, GraphQL.Execution.completeValueList]
        apply runMatches_bind _ _ _ _ _
          (completeValue_inContext usage hvalid deferMap schema resolvers variables fuel itemType
            fields value hplain
            (path ++ [ResponsePathSegment.index index]) false state)
        intro head hh
        apply runMatches_bind _ _ _ _ _
          (completeListValue_inContext usage hvalid deferMap schema resolvers variables fuel
            itemType fields rest hplain
            path (index + 1) state)
        intro tail ht
        apply runMatches_pure
        exact completionMatches_combine List.cons head tail _ _ hh ht
  termination_by (fuel, 2, sizeOf itemType, sizeOf values)
  decreasing_by
    all_goals
      subst_vars
      simp_wf
      repeat first
        | apply Prod.Lex.left; omega
        | apply Prod.Lex.right
      try omega
end

end GraphQL.IncrementalDelivery.Semantics
