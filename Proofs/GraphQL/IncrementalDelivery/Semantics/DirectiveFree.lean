import Proofs.GraphQL.IncrementalDelivery.Semantics.Completion

/-! Basic-execution agreement for operations without incremental directives. -/

namespace GraphQL.IncrementalDelivery.Semantics

open GraphQL.IncrementalDelivery.Execution

attribute [local simp] id_pure_eq id_bind_eq id_map_eq run_bind run_map

variable {ObjectRef : Type}

mutual
  /-- Plain groups agree with basic execution without work; mutual induction combines
  fields.
  -/
  theorem executeCollectedFields_plain (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variables : VariableValues) (fuel : Nat) (parentType : Name)
      (source : ResolverValue ObjectRef)
      (groups : CollectedFieldsMap) (hplain : GroupsPlain groups) (path : ResponsePath)
      (state : Nat)
      : RunMatches
          (executeCollectedFields schema resolvers variables fuel parentType source groups
            path [] [])
          (GraphQL.Execution.executeCollectedFields schema resolvers variables fuel
            parentType source (eraseGroups groups))
          state := by
    cases groups with
    | nil =>
        simp [executeCollectedFields_nil, GraphQL.Execution.executeCollectedFields,
        eraseGroups, RunMatches, CompletionMatches, Completion.pure, Work.size]
    | cons group rest =>
        rcases group with ⟨name, fields⟩
        have hf : FieldsPlain fields := hplain (name, fields) (by simp)
        have hr : GroupsPlain rest := fun g h => hplain g (by simp [h])
        simp only [executeCollectedFields_cons, eraseGroups, List.map_cons, eraseGroup,
          GraphQL.Execution.executeCollectedFields]
        apply runMatches_bind _ _ _ _ _
          (executeResponseField_plain schema resolvers variables fuel parentType source
            name fields hf path
            state)
        intro head hh
        apply runMatches_bind _ _ _ _ _
          (executeCollectedFields_plain schema resolvers variables fuel parentType source
            rest hr path state)
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

  /-- Plain fields agree with basic execution; mutual induction covers errors and values.
  -/
  theorem executeResponseField_plain (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variables : VariableValues) (fuel : Nat) (parentType : Name)
      (source : ResolverValue ObjectRef)
      (name : Name) (fields : List ExecutableField) (hplain : FieldsPlain fields)
      (path : ResponsePath) (state : Nat)
      : RunMatches
          (executeResponseField schema resolvers variables fuel parentType source name
            fields path [] [])
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
                          (completeValue_plain schema resolvers variables fuel definition.outputType
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

  /-- Plain completion agrees for every wrapper/value; mutual induction on fuel/type
  structure.
  -/
  theorem completeValue_plain (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variables : VariableValues) (fuel : Nat) (fieldType : TypeRef)
      (fields : List ExecutableField) (value : ResolverValue ObjectRef)
      (hplain : FieldsPlain fields) (path : ResponsePath) (allowStream : Bool)
      (state : Nat)
      : RunMatches
          (completeValue schema resolvers variables fuel fieldType fields value path [] []
            allowStream)
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
              (completeValue_plain schema resolvers variables (fuel + 1) inner fields value hplain
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
                  apply runMatches_after_collection _ _ _ _ _
                    (collectSubfields_plain schema variables runtimeType (.object runtimeType ref)
                      fields hplain state)
                  intro collection hn hp he
                  apply runMatches_bind _ _ _ _ _
                    (executePlan_plain schema resolvers variables fuel runtimeType
                      (.object runtimeType ref) collection path state _ hn hp
                      (executeCollectedFields_plain schema resolvers variables fuel
                        runtimeType (.object runtimeType ref) collection.fields hp path state))
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
                have hs := streamUsage_plain variables fields hplain
                have hs' : (if allowStream then
                    getStreamUsage variables
                      (fields.head?.map ExecutableField.directives |>.getD [])
                    else .ok none) = .ok none := by simp [hs]
                simp only [hs']
                apply runMatches_bind _ _ _ _ _
                  (completeListValue_plain schema resolvers variables fuel inner fields
                    items hplain path 0 state)
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

  /-- Plain lists complete like basic lists without work; mutual induction combines item
  witnesses.
  -/
  theorem completeListValue_plain (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variables : VariableValues) (fuel : Nat) (itemType : TypeRef)
      (fields : List ExecutableField) (values : List (ResolverValue ObjectRef))
      (hplain : FieldsPlain fields) (path : ResponsePath) (index state : Nat)
      : RunMatches
          (completeListValue schema resolvers variables fuel itemType fields values
            path index [] [])
          (GraphQL.Execution.completeValueList schema resolvers variables fuel itemType
            (fields.map eraseField) values)
          state := by
    cases values with
    | nil => simp [completeListValue, GraphQL.Execution.completeValueList, RunMatches,
        CompletionMatches, Completion.pure, Work.size]
    | cons value rest =>
        simp only [completeListValue, GraphQL.Execution.completeValueList]
        apply runMatches_bind _ _ _ _ _
          (completeValue_plain schema resolvers variables fuel itemType fields value hplain
            (path ++ [ResponsePathSegment.index index]) false state)
        intro head hh
        apply runMatches_bind _ _ _ _ _
          (completeListValue_plain schema resolvers variables fuel itemType fields rest hplain
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
