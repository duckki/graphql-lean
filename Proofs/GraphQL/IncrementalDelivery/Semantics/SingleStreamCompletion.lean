import Proofs.GraphQL.IncrementalDelivery.Semantics.ContextCompletion
import Proofs.GraphQL.IncrementalDelivery.Semantics.BasicErrors

/-! Ordinary streamed items agree with basic completion, including the exact
short-circuit boundary of a failed streamed item. Outer field directives are
unrestricted because item completion explicitly disables streaming. -/

namespace GraphQL.IncrementalDelivery.Semantics

open GraphQL.IncrementalDelivery.Execution

attribute [local simp] id_pure_eq id_bind_eq id_map_eq run_bind run_map

variable {ObjectRef : Type}

/-- Plain item selections, with no restriction on the outer field directives. -/
abbrev ItemFieldsInContext (usage : Option DeferUsage) (fields : List ExecutableField)
    : Prop :=
  ∀ field ∈ fields, field.deferUsage = usage ∧ SelectionsPlain field.selectionSet

theorem collectSubfields_itemContext (schema : Schema) (variables : VariableValues)
    (parentType : Name) (source : ResolverValue ObjectRef) (fields : List ExecutableField)
    (usage : Option DeferUsage) (hfields : ItemFieldsInContext usage fields) (state : Nat)
    : CollectionInContext usage state
        ((collectSubfields schema variables parentType source fields).run state) := by
  induction fields with
  | nil => simp [collectSubfields, CollectionInContext, GroupsInContext]
  | cons field rest ih =>
      have hf := hfields field (by simp)
      have hr : ItemFieldsInContext usage rest := fun f h => hfields f (by simp [h])
      have hh := collectFields_inContext schema variables parentType source field.selectionSet
        hf.2 usage state
      have ht := ih hr
      generalize hhout :
        (collectFields schema variables parentType source field.selectionSet usage).run state
        = headPair at hh
      generalize htout : (collectSubfields schema variables parentType source rest).run state
        = tailPair at ht
      rcases headPair with ⟨head, next⟩
      rcases tailPair with ⟨tail, final⟩
      rcases hh with ⟨hnext, hhn, hhp⟩
      rcases ht with ⟨hfinal, htn, htp⟩
      dsimp only at hnext hfinal
      subst next final
      have hp := collectionInContext_append usage ⟨rfl, hhn, hhp⟩ ⟨rfl, htn, htp⟩
      simpa [collectSubfields, hf.1, run_bind, run_map, hhout, htout] using hp

mutual
  theorem completeValue_itemContext (usage : Option DeferUsage)
      (hvalid : ContextWellFormed usage) (deferMap : DeferMap) (schema : Schema)
      (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
      (fieldType : TypeRef) (fields : List ExecutableField)
      (value : ResolverValue ObjectRef) (hplain : ItemFieldsInContext usage fields)
      (path : ResponsePath) (state : Nat)
      : RunMatches
          (completeValue schema resolvers variables fuel fieldType fields value path
            (contextKeys usage) deferMap false)
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
              (completeValue_itemContext usage hvalid deferMap schema resolvers variables (fuel + 1)
                inner fields value hplain
                path state)
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
                    (collectSubfields_itemContext schema variables runtimeType (.object runtimeType
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
                simp only [Bool.false_eq_true, ↓reduceIte]
                apply runMatches_bind _ _ _ _ _
                  (completeListValue_itemContext usage hvalid deferMap schema resolvers variables
                    fuel inner fields items
                    hplain path 0 state)
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

  theorem completeListValue_itemContext (usage : Option DeferUsage)
      (hvalid : ContextWellFormed usage) (deferMap : DeferMap) (schema : Schema)
      (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
      (itemType : TypeRef) (fields : List ExecutableField)
      (values : List (ResolverValue ObjectRef))
      (hplain : ItemFieldsInContext usage fields) (path : ResponsePath)
      (index state : Nat)
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
          (completeValue_itemContext usage hvalid deferMap schema resolvers variables fuel itemType
            fields value hplain
            (path ++ [ResponsePathSegment.index index]) state)
        intro head hh
        apply runMatches_bind _ _ _ _ _
          (completeListValue_itemContext usage hvalid deferMap schema resolvers variables fuel
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

/-- Basic item completions, stopping immediately after the first bubbled error.
Successful results with a positive error count do not stop the stream. -/
def basicStreamResults (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues) (fuel : Nat) (itemType : TypeRef)
    (fields : List ExecutableField)
    : List (ResolverValue ObjectRef) → List (Result ResponseValue)
  | [] => []
  | value :: rest =>
      let result :=
        GraphQL.Execution.completeValue schema resolvers variables fuel
          itemType (fields.map eraseField) value
      match result with
      | .error _ => [result]
      | .ok _ =>
          result
          :: basicStreamResults schema resolvers variables fuel itemType fields rest

theorem completeStreamItems_itemContext (schema : Schema)
    (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
    (itemType : TypeRef) (fields : List ExecutableField)
    (values : List (ResolverValue ObjectRef)) (hplain : ItemFieldsInContext none fields)
    (path : ResponsePath) (index state : Nat)
    : let output :=
        (completeStreamItems schema resolvers variables fuel itemType fields
          values path index).run
          state
      output.2 = state
      ∧ output.1.map Prod.fst
        = basicStreamResults schema resolvers variables fuel itemType fields values
      ∧ ∀ item ∈ output.1, Work.size item.2 = 0 := by
  induction values generalizing index state with
  | nil => simp [completeStreamItems, basicStreamResults]
  | cons value rest ih =>
      have hh := completeValue_itemContext none (by simp [ContextWellFormed]) []
        schema resolvers variables fuel itemType fields value hplain
        (path ++ [.index index]) state
      simp only [RunMatches, CompletionMatches, contextKeys, Option.toList_none,
        List.map_nil] at hh
      generalize he : (completeValue schema resolvers variables fuel itemType fields value
        (path ++ [.index index]) [] [] false).run state = pair at hh
      rcases pair with ⟨head, next⟩
      rcases hh with ⟨hstate, hr, hw⟩
      dsimp only at hstate hr hw
      subst next
      cases hb
            : GraphQL.Execution.completeValue schema resolvers variables fuel itemType
                (fields.map eraseField) value with
      | error errors =>
          simp [completeStreamItems, he, hr, hb, basicStreamResults, Work.size]
      | ok result =>
          have ht := ih (index + 1) state
          generalize htout : (completeStreamItems schema resolvers variables fuel itemType fields
            rest path (index + 1)).run state = tailPair at ht
          rcases tailPair with ⟨tail, final⟩
          rcases ht with ⟨hfinal, hresults, hsilent⟩
          dsimp only at hfinal hresults hsilent
          subst final
          simp only [completeStreamItems, run_bind, he, hr, hb, htout,
            StateT.run_pure, id_pure_eq, List.map_cons, basicStreamResults]
          exact ⟨True.intro, congrArg (List.cons (.ok result)) hresults,
            fun item hi => by
              rcases List.mem_cons.mp hi with rfl | hi
              · exact hw
              · exact hsilent item hi⟩

theorem basicStreamResults_success (schema : Schema)
    (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
    (itemType : TypeRef) (fields : List ExecutableField)
    (values : List (ResolverValue ObjectRef)) (data : List ResponseValue)
    (hsuccess
      : basicStreamResults schema resolvers variables fuel itemType fields values
        = data.map (fun value => (.ok (value, 0) : Result ResponseValue)))
    : GraphQL.Execution.completeValueList schema resolvers variables fuel itemType
        (fields.map eraseField) values
      = .ok (data, 0) := by
  induction values generalizing data with
  | nil =>
      cases data <;> simp_all [basicStreamResults, GraphQL.Execution.completeValueList]
  | cons value rest ih =>
      cases hb
            : GraphQL.Execution.completeValue schema resolvers variables fuel itemType
                (fields.map eraseField) value with
      | error errors =>
          cases data <;> simp_all [basicStreamResults]
      | ok result =>
          cases data with
          | nil => simp [basicStreamResults, hb] at hsuccess
          | cons datum data =>
              simp only [basicStreamResults, hb, List.map_cons, List.cons.injEq,
                Except.ok.injEq] at hsuccess
              rcases hsuccess with ⟨rfl, ht⟩
              simp [GraphQL.Execution.completeValueList, hb, ih data ht,
                GraphQL.Execution.Result.combine]

theorem completeStreamItems_success (schema : Schema)
    (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
    (itemType : TypeRef) (fields : List ExecutableField)
    (values : List (ResolverValue ObjectRef)) (hplain : ItemFieldsInContext none fields)
    (path : ResponsePath) (index state : Nat) (data : List ResponseValue)
    (hsuccess
      : ((completeStreamItems schema resolvers variables fuel itemType fields values
            path index).run
          state).1.map
          Prod.fst
        = data.map (fun value => (.ok (value, 0) : Result ResponseValue)))
    : GraphQL.Execution.completeValueList schema resolvers variables fuel itemType
        (fields.map eraseField) values
      = .ok (data, 0) := by
  apply basicStreamResults_success schema resolvers variables fuel itemType fields values data
  rw [← (completeStreamItems_itemContext schema resolvers variables fuel itemType fields
    values hplain path index state).2.1]
  exact hsuccess

theorem basicStreamResults_positive (schema : Schema)
    (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
    (itemType : TypeRef) (fields : List ExecutableField)
    (values : List (ResolverValue ObjectRef))
    : ∀ result ∈
        basicStreamResults schema resolvers variables fuel itemType fields values,
        BasicErrors.PositiveFailure result := by
  induction values with
  | nil => simp [basicStreamResults]
  | cons value rest ih =>
      have hp := BasicErrors.completeValue schema resolvers variables fuel itemType
        (fields.map eraseField) value
      cases hb : GraphQL.Execution.completeValue schema resolvers variables fuel itemType
          (fields.map eraseField) value <;>
        simp_all [basicStreamResults]

theorem basicCompleteValueList_positive (schema : Schema)
    (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
    (itemType : TypeRef) (fields : List GraphQL.Execution.ExecutableField)
    (values : List (ResolverValue ObjectRef))
    : BasicErrors.PositiveFailure
        (GraphQL.Execution.completeValueList schema resolvers variables fuel itemType
          fields values) := by
  induction values with
  | nil => simp [GraphQL.Execution.completeValueList, BasicErrors.PositiveFailure]
  | cons value rest ih =>
      simp only [GraphQL.Execution.completeValueList]
      exact BasicErrors.combine List.cons _ _
        (BasicErrors.completeValue schema resolvers variables fuel itemType fields value) ih

theorem basicCompleteValueList_append (schema : Schema)
    (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
    (itemType : TypeRef) (fields : List GraphQL.Execution.ExecutableField)
    (left right : List (ResolverValue ObjectRef))
    : GraphQL.Execution.completeValueList schema resolvers variables fuel itemType fields
        (left ++ right)
      = GraphQL.Execution.Result.combine List.append
          (GraphQL.Execution.completeValueList schema resolvers variables fuel itemType
            fields left)
          (GraphQL.Execution.completeValueList schema resolvers variables fuel itemType
            fields right) := by
  induction left with
  | nil =>
      simp only [List.nil_append, GraphQL.Execution.completeValueList]
      cases GraphQL.Execution.completeValueList schema resolvers variables fuel itemType fields right <;>
        simp [GraphQL.Execution.Result.combine]
  | cons value rest ih =>
      simp only [List.cons_append, GraphQL.Execution.completeValueList, ih]
      cases GraphQL.Execution.completeValue schema resolvers variables fuel itemType fields value <;>
        cases GraphQL.Execution.completeValueList schema resolvers variables fuel itemType fields rest <;>
        cases GraphQL.Execution.completeValueList schema resolvers variables fuel itemType fields right <;>
        simp [GraphQL.Execution.Result.combine, List.cons_append, Nat.add_assoc]

theorem eraseFields_clearDefer (fields : List ExecutableField)
    : (fields.map (fun field => { field with deferUsage := none })).map eraseField
      = fields.map eraseField := by
  simp [List.map_map, eraseField]

theorem itemFields_clearDefer (usage : Option DeferUsage) (fields : List ExecutableField)
    (hplain : ItemFieldsInContext usage fields)
    : ItemFieldsInContext none
        (fields.map (fun field => { field with deferUsage := none })) := by
  intro field hf
  rcases List.mem_map.mp hf with ⟨original, ho, rfl⟩
  exact ⟨rfl, (hplain original ho).2⟩

theorem completeList_split_success (usage : Option DeferUsage)
    (hvalid : ContextWellFormed usage) (deferMap : DeferMap) (schema : Schema)
    (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
    (itemType : TypeRef) (fields : List ExecutableField)
    (values : List (ResolverValue ObjectRef)) (hplain : ItemFieldsInContext usage fields)
    (path : ResponsePath) (count state : Nat) (initialData tail : List ResponseValue)
    (hinitial
      : ((completeListValue schema resolvers variables fuel itemType fields
            (values.take count) path 0 (contextKeys usage) deferMap).run
          state).1.result
        = .ok (initialData, 0))
    (htail
      : ((completeStreamItems schema resolvers variables fuel itemType
            (fields.map (fun field => { field with deferUsage := none }))
            (values.drop count) path count).run
          (state + 1)).1.map
          Prod.fst
        = tail.map (fun value => (.ok (value, 0) : Result ResponseValue)))
    : GraphQL.Execution.completeValueList schema resolvers variables fuel itemType
        (fields.map eraseField) values
      = .ok (initialData ++ tail, 0) := by
  have hi := (completeListValue_itemContext usage hvalid deferMap schema resolvers variables fuel
    itemType fields (values.take count) hplain path 0 state).2.1.symm.trans hinitial
  have ht := completeStreamItems_success schema resolvers variables fuel itemType _
    (values.drop count) (itemFields_clearDefer usage fields hplain) path count (state + 1)
    tail htail
  rw [eraseFields_clearDefer] at ht
  have hsplit := basicCompleteValueList_append schema resolvers variables fuel itemType
    (fields.map eraseField) (values.take count) (values.drop count)
  simpa [List.take_append_drop, hi, ht, GraphQL.Execution.Result.combine] using hsplit

theorem completeListValueWithStream_stream_run (usage : Option DeferUsage)
    (hvalid : ContextWellFormed usage) (deferMap : DeferMap) (schema : Schema)
    (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
    (itemType : TypeRef) (fields : List ExecutableField)
    (values : List (ResolverValue ObjectRef)) (hplain : ItemFieldsInContext usage fields)
    (path : ResponsePath) (stream : StreamUsage) (state : Nat)
    (hstream
      : getStreamUsage variables (fields.head?.map ExecutableField.directives |>.getD [])
        = .ok (some stream))
    : (completeListValueWithStream schema resolvers variables fuel itemType fields values
        path (contextKeys usage) deferMap true).run
        state
      = let initial :=
          ((completeListValue schema resolvers variables fuel itemType fields
              (values.take stream.initialCount) path 0 (contextKeys usage) deferMap).run
            state).1
        match initial.result with
        | .error _ => (initial.catchNull ResponseValue.list, state)
        | .ok _ =>
            if (values.drop stream.initialCount).isEmpty then
              (initial.catchNull ResponseValue.list, state)
            else
              let items :=
                ((completeStreamItems schema resolvers variables fuel itemType
                    (fields.map (fun field => { field with deferUsage := none }))
                    (values.drop stream.initialCount) path stream.initialCount).run
                  (state + 1)).1
              (
                {
                  (initial.catchNull ResponseValue.list) with
                    work :=
                      .append initial.work
                        (.stream { key := state, path := path, label := stream.label }
                          items)
                },
                state + 1
              ) := by
  have hi := completeListValue_itemContext usage hvalid deferMap schema resolvers variables fuel
    itemType fields (values.take stream.initialCount) hplain path 0 state
  have ht := completeStreamItems_itemContext schema resolvers variables fuel itemType _
    (values.drop stream.initialCount) (itemFields_clearDefer usage fields hplain)
    path stream.initialCount (state + 1)
  simp only [RunMatches] at hi
  generalize he : (completeListValue schema resolvers variables fuel itemType fields
    (values.take stream.initialCount) path 0 (contextKeys usage) deferMap).run state = initialPair at hi ⊢
  rcases initialPair with ⟨initial, next⟩
  have hnext := hi.1
  dsimp only at hnext
  subst next
  generalize heitems : (completeStreamItems schema resolvers variables fuel itemType
    (fields.map (fun field => { field with deferUsage := none }))
    (values.drop stream.initialCount) path stream.initialCount).run (state + 1) = itemsPair at ht ⊢
  rcases itemsPair with ⟨items, final⟩
  have hfinal := ht.1
  dsimp only at hfinal
  subst final
  cases hr : initial.result <;>
    by_cases hempty : values.length ≤ stream.initialCount <;>
      simp [completeListValueWithStream, hstream, he, hr, freshExecutionKey, heitems,
        Completion.catchNull, hempty]

theorem catchNull_result_ok (completed : Completion α) (wrap : α → ResponseValue)
    : ∃ value errors, (completed.catchNull wrap).result = .ok (value, errors) := by
  cases hr : completed.result <;> simp [Completion.catchNull, hr]

theorem completeListValueWithStream_result_ok (schema : Schema)
    (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
    (itemType : TypeRef) (fields : List ExecutableField)
    (values : List (ResolverValue ObjectRef)) (path : ResponsePath)
    (deferUsageSet : List Nat) (deferMap : DeferMap) (allowStream : Bool) (state : Nat)
    : ∃ value errors,
        ((completeListValueWithStream schema resolvers variables fuel itemType fields
            values path deferUsageSet deferMap allowStream).run
          state).1.result
        = .ok (value, errors) := by
  cases hs
        : (if allowStream then
              getStreamUsage variables
                (fields.head?.map ExecutableField.directives |>.getD [])
            else
              .ok none) with
  | error errors => simp [completeListValueWithStream, hs]
  | ok stream =>
      simp only [completeListValueWithStream, hs]
      cases stream with
      | none =>
          simp only [run_bind, StateT.run_pure, id_pure_eq]
          exact catchNull_result_ok _ _
      | some stream =>
          simp only [run_bind]
          split
          · simp only [StateT.run_pure, id_pure_eq]
            exact catchNull_result_ok _ _
          · split
            · simp only [StateT.run_pure, id_pure_eq]
              exact catchNull_result_ok _ _
            · simp only [run_bind, StateT.run_pure, id_pure_eq]
              exact catchNull_result_ok _ _

theorem completeValue_error_silent (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues) (fuel : Nat) (fieldType : TypeRef)
    (fields : List ExecutableField) (value : ResolverValue ObjectRef)
    (path : ResponsePath) (deferUsageSet : List Nat) (deferMap : DeferMap)
    (allowStream : Bool) (state errors : Nat)
    (herror
      : ((completeValue schema resolvers variables fuel fieldType fields value
            path deferUsageSet deferMap allowStream).run
          state).1.result
        = .error errors)
    : Work.size
        ((completeValue schema resolvers variables fuel fieldType fields value
            path deferUsageSet deferMap allowStream).run
          state).1.work
      = 0 := by
  cases fuel with
  | zero => simp [completeValue, Completion.error, Work.size]
  | succ fuel =>
      cases fieldType with
      | nonNull inner =>
          simp only [completeValue, run_bind, StateT.run_pure, id_pure_eq] at herror ⊢
          unfold Completion.nonNull at herror ⊢
          split at herror <;> simp_all [Completion.error, Work.size]
      | named parentType =>
          cases value with
          | null => simp [completeValue, Completion.pure] at herror
          | scalar scalar =>
              simp only [completeValue]
              split <;> rfl
          | list values => simp [completeValue, Completion.error, Work.size]
          | object runtimeType ref =>
              simp only [completeValue] at herror ⊢
              split at herror
              · simp_all [Completion.error, Work.size]
              · simp only [run_bind, StateT.run_pure, id_pure_eq] at herror
                obtain ⟨value, count, h⟩ := catchNull_result_ok
                  ((executeExecutionPlan schema resolvers variables fuel runtimeType
                    (.object runtimeType ref)
                    ((collectSubfields schema variables runtimeType (.object runtimeType ref)
                      fields).run state).1.newDeferUsages
                    (buildExecutionPlan
                      ((collectSubfields schema variables runtimeType (.object runtimeType ref)
                        fields).run state).1.fields deferUsageSet)
                    path deferUsageSet deferMap).run
                    ((collectSubfields schema variables runtimeType (.object runtimeType ref)
                      fields).run state).2).1 ResponseValue.object
                rw [h] at herror
                contradiction
      | list inner =>
          cases value with
          | null => simp [completeValue, Completion.pure] at herror
          | scalar scalar =>
              simp [completeValue, Completion.error, Work.size]
          | object runtimeType ref =>
              simp [completeValue, Completion.error, Work.size]
          | list values =>
              obtain ⟨value, count, h⟩ := completeListValueWithStream_result_ok schema
                resolvers variables fuel
                inner fields values path deferUsageSet deferMap allowStream state
              simp only [completeValue] at herror
              rw [h] at herror
              contradiction

theorem getStreamUsage_error_count (variables : VariableValues)
    (directives : List DirectiveApplication) (errors : Nat)
    (herror : getStreamUsage variables directives = .error errors)
    : errors = 1 := by
  induction directives with
  | nil => simp [getStreamUsage] at herror
  | cons directive rest ih =>
      cases directive with
      | skip condition => exact ih herror
      | «include» condition => exact ih herror
      | defer condition label => exact ih herror
      | stream condition label count =>
          simp only [getStreamUsage] at herror
          split at herror
          · contradiction
          · split at herror <;> simp_all

end GraphQL.IncrementalDelivery.Semantics
