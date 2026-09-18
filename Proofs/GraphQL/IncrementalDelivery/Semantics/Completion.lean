import Proofs.GraphQL.IncrementalDelivery.Semantics.Collection

/-! Silent-completion invariants and their preservation by execution combinators. -/

namespace GraphQL.IncrementalDelivery.Semantics

open GraphQL.IncrementalDelivery.Execution

attribute [local simp] id_pure_eq id_bind_eq id_map_eq run_bind run_map

variable {ObjectRef : Type}

def CompletionMatches (basic : Result α) (completed : Completion α) : Prop :=
  completed.result = basic ∧ Work.size completed.work = 0

def RunMatches (action : StateM Nat (Completion α)) (basic : Result α) (state : Nat)
    : Prop :=
  (action.run state).2 = state ∧ CompletionMatches basic (action.run state).1

/-- A pure matching completion preserves the supply; witness: the input match and
reflexivity.
-/
theorem runMatches_pure (completed : Completion α) (basic : Result α) (state : Nat)
    (h : CompletionMatches basic completed)
    : RunMatches (pure completed) basic state :=
  ⟨rfl, h⟩

/-- Sequencing matching completions preserves result and supply, by substituting the
unchanged state.
-/
theorem runMatches_bind (action : StateM Nat (Completion α)) (basic : Result α)
    (next : Completion α → StateM Nat (Completion β)) (target : Result β) (state : Nat)
    (h : RunMatches action basic state)
    (hn
      : ∀ completed,
          CompletionMatches basic completed → RunMatches (next completed) target state)
    : RunMatches (action >>= next) target state := by
  unfold RunMatches at h
  generalize hout : action.run state = output at h
  rcases output with ⟨completed, final⟩
  rcases h with ⟨hstate, hc⟩
  dsimp only at hstate
  subst final
  simpa [RunMatches, hout] using hn completed hc

/-- Combining silent completions matches basic result combination, by result case
analysis.
-/
theorem completionMatches_combine (f : α → β → γ) (left : Completion α)
    (right : Completion β) (basicLeft : Result α) (basicRight : Result β)
    (hl : CompletionMatches basicLeft left) (hr : CompletionMatches basicRight right)
    : CompletionMatches (GraphQL.Execution.Result.combine f basicLeft basicRight)
        (Completion.combine f left right) := by
  rcases hl with ⟨hlr, hlw⟩
  rcases hr with ⟨hrr, hrw⟩
  cases basicLeft <;> cases basicRight <;>
    simp_all [CompletionMatches, Completion.combine, GraphQL.Execution.Result.combine,
      Completion.error, Work.size]

/-- Non-null completion preserves basic agreement and silence, by inspecting its bubbling
result.
-/
theorem completionMatches_nonNull (completed : Completion ResponseValue)
    (basic : Result ResponseValue) (h : CompletionMatches basic completed)
    : CompletionMatches (nonNullCompletion basic) completed.nonNull := by
  rcases h with ⟨hr, hw⟩
  simp only [Completion.nonNull, hr]
  cases hb : nonNullCompletion basic <;>
    simp [CompletionMatches, Completion.error, Work.size, hw]

/-- Catching a bubble preserves basic agreement and silence, by error/success case
analysis.
-/
theorem completionMatches_catchNull (wrap : α → ResponseValue)
    (completed : Completion α) (basic : Result α) (h : CompletionMatches basic completed)
    : CompletionMatches (GraphQL.Execution.catchBubbleAsNull wrap basic)
        (completed.catchNull wrap) := by
  rcases h with ⟨hr, hw⟩
  cases basic <;>
    simp_all [CompletionMatches, Completion.catchNull,
      GraphQL.Execution.catchBubbleAsNull, Work.size]

/-- Wrapping a completed field preserves basic agreement and silence, by result case
analysis.
-/
theorem completionMatches_field (name : Name) (completed : Completion ResponseValue)
    (basic : Result ResponseValue) (h : CompletionMatches basic completed)
    : CompletionMatches (singleFieldResult name basic)
        (completed.map (fun value => [(name, value)])) := by
  rcases h with ⟨hr, hw⟩
  cases basic <;>
    simp_all [CompletionMatches, Completion.map, singleFieldResult,
      Completion.error, Work.size]

/-- Plain collection can feed a matching continuation, using its unchanged-state witness.
-/
theorem runMatches_after_collection (action : StateM Nat FieldCollection)
    (groups : List (Name × List GraphQL.Execution.ExecutableField))
    (next : FieldCollection → StateM Nat (Completion α)) (basic : Result α) (state : Nat)
    (h : CollectionMatches groups state (action.run state))
    (hn
      : ∀ collection,
          collection.newDeferUsages = []
          → GroupsPlain collection.fields
          → eraseGroups collection.fields = groups
          → RunMatches (next collection) basic state)
    : RunMatches (action >>= next) basic state := by
  generalize hout : action.run state = output at h
  rcases output with ⟨collection, final⟩
  rcases h with ⟨hstate, hnw, hp, he⟩
  dsimp only at hstate
  subst final
  simpa [RunMatches, hout] using hn collection hnw hp he

/-- Plain plan execution creates no deferred work, by buildExecutionPlan_plain and the
field witness.
-/
theorem executePlan_plain (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues) (fuel : Nat) (parentType : Name)
    (source : ResolverValue ObjectRef)
    (collection : FieldCollection) (path : ResponsePath) (state : Nat) (basic : Result _)
    (hn : collection.newDeferUsages = []) (hp : GroupsPlain collection.fields)
    (hr
      : RunMatches
          (executeCollectedFields schema resolvers variables fuel parentType source
            collection.fields path [] [])
          basic state)
    : RunMatches
        (executeExecutionPlan schema resolvers variables fuel parentType source
          collection.newDeferUsages (buildExecutionPlan collection.fields) path [] [])
        basic state := by
  simp only [executeExecutionPlan, hn, getNewDeferMap, List.foldl_nil,
    buildExecutionPlan_plain collection.fields hp]
  apply runMatches_bind _ _ _ _ _ hr
  intro completed hc
  cases he : completed.result with
  | error errors =>
      simpa [he] using runMatches_pure completed basic state hc
  | ok result =>
      simp only [collectExecutionGroups]
      apply runMatches_pure
      exact ⟨by simpa [he] using hc.1, by simpa [Work.size] using hc.2⟩

/-- Plain fields request no streaming, by the head field's directives_plain witness. -/
theorem streamUsage_plain (variables : VariableValues) (fields : List ExecutableField)
    (h : FieldsPlain fields)
    : getStreamUsage variables (fields.head?.map ExecutableField.directives |>.getD [])
      = .ok none := by
  cases fields with
  | nil => rfl
  | cons field rest =>
      exact (directives_plain variables field.directives (h field (by simp)).2.1).2.2

end GraphQL.IncrementalDelivery.Semantics
