import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.SiblingCuts

/-! Construct a permitted scope history from the same executed action prefix.
This discharges the history premise for sequential atomic cuts, not native races,
recursive cancellation inside actions, or originating-error recording before settlement.
-/

namespace
  GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.ScheduledErrors

open GraphQL.IncrementalDelivery.Execution

-----------------------------------------------------------------------------------------
-- Prefix shape is derived from executed outcomes, not assumed response agreement
-----------------------------------------------------------------------------------------

inductive CutPrefix : List (Sibling α) → List (Sibling α) → Prop where
  | empty : CutPrefix [] []
  | fatal (sibling : Sibling α) (omitted : List (Sibling α))
    (failed : isFatal sibling.outcome = true)
    : CutPrefix [sibling] omitted
  | success (sibling : Sibling α) {completed omitted}
    (healthy : isFatal sibling.outcome = false) (later : CutPrefix completed omitted)
    : CutPrefix (sibling :: completed) omitted

theorem completionPlan_append (left right : List (Completion α)) (id : Nat)
    : completionPlan (left ++ right) id
      = completionPlan left id ++ completionPlan right (id + left.length) := by
  induction left generalizing id with
  | nil => simp [completionPlan]
  | cons head rest ih =>
      simp only [List.cons_append, completionPlan, List.length_cons]
      rw [ih]
      have same : (id + 1) + rest.length = id + (rest.length + 1) := by omega
      rw [same]

/-- The cut supplies both its prefix shape and the hypothetical eager omitted outcomes. -/
theorem ActionCut.prefix {actions : List (StateM Nat (Completion α))}
    {supply completed remaining next}
    (cut : ActionCut actions supply completed remaining next) (id : Nat)
    : CutPrefix (completionPlan completed id)
        (completionPlan ((observeActions remaining).run next).1
          (id + completed.length)) := by
  induction cut generalizing id with
  | empty => exact .empty
  | fatal action rest supply completed next errors ran failed =>
      exact .fatal _ _ (by simp [failed, isFatal])
  | success action rest supply completed next observed remaining finish value errors
      ran succeeded later ih =>
      have same : id + (completed :: observed).length = (id + 1) + observed.length := by
        simp only [List.length_cons]
        omega
      rw [same]
      exact .success _ (by simp [succeeded, isFatal]) (ih (id + 1))

-----------------------------------------------------------------------------------------
-- Construct start/settle actions for the prefix and cancellation for its suffix
-----------------------------------------------------------------------------------------

private theorem cancel_suffix {plan : List (Sibling α)} {scope : Scope α}
    (history : History plan scope) (omitted : List (Sibling α))
    (pending : scope.pending = omitted) (failed : scope.fatal = true)
    : ∃ final,
        History plan final
        ∧ final.pending = []
        ∧ final.settled = scope.settled
        ∧ final.cancelled = scope.cancelled ++ omitted
        ∧ final.actions
          = scope.actions ++ omitted.map (fun sibling => .cancel sibling.id) := by
  induction omitted generalizing scope with
  | nil => exact ⟨scope, history, pending, rfl, (List.append_nil _).symm,
      (List.append_nil _).symm⟩
  | cons sibling rest ih =>
      have cancelled : History plan (scope.cancel [] sibling rest) :=
        .cancel history [] rest sibling pending failed
      obtain ⟨final, valid, complete, settled, cancelledAll, actions⟩ :=
        ih cancelled rfl failed
      refine ⟨final, valid, complete, settled, ?_, ?_⟩
      · simpa only [Scope.cancel, List.append_assoc, List.singleton_append] using cancelledAll
      · simpa only [Scope.cancel, List.map_cons, List.append_assoc, List.singleton_append]
          using actions

/-- A finite constructor, not a conditional reduction from a desired scope outcome. -/
private theorem CutPrefix.scope_history {plan : List (Sibling α)} {scope : Scope α}
    {completed omitted : List (Sibling α)} (cut : CutPrefix completed omitted)
    (history : History plan scope) (pending : scope.pending = completed ++ omitted)
    (running : scope.fatal = false)
    (unique : ((completed ++ omitted).map Sibling.id).Nodup)
    (fresh : ∀ sibling ∈ completed ++ omitted, sibling.id ∉ scope.started)
    : ∃ final,
        History plan final
        ∧ final.pending = []
        ∧ final.settled = scope.settled ++ completed
        ∧ final.cancelled = scope.cancelled ++ omitted
        ∧ final.actions
          = scope.actions
            ++ completed.flatMap (fun sibling => [.start sibling.id, .settle sibling.id])
            ++ omitted.map (fun sibling => .cancel sibling.id) := by
  induction cut generalizing scope with
  | empty =>
      exact ⟨
        scope,
        history,
        pending,
        (List.append_nil _).symm,
        (List.append_nil _).symm,
        (by simp)
      ⟩
  | fatal sibling omitted failed =>
      have member : sibling ∈ scope.pending := by rw [pending]; simp
      have started : History plan (scope.start sibling.id) :=
        .start history sibling member running (fresh sibling (by simp))
      have settled : History plan ((scope.start sibling.id).settle [] sibling omitted) :=
        .settle started [] omitted sibling pending (by simp [Scope.start])
      obtain ⟨final, valid, complete, settledAll, cancelled, actions⟩ :=
        cancel_suffix settled omitted rfl (by simp [Scope.settle, failed])
      refine ⟨final, valid, complete, settledAll, cancelled, ?_⟩
      simpa only [Scope.settle, Scope.start, List.flatMap_cons, List.flatMap_nil,
        List.append_nil, List.append_assoc, List.singleton_append]
        using actions
  | success sibling healthy later ih =>
      rename_i tail skipped
      have member : sibling ∈ scope.pending := by rw [pending]; simp
      have started : History plan (scope.start sibling.id) :=
        .start history sibling member running (fresh sibling (by simp))
      have settled
          : History plan ((scope.start sibling.id).settle [] sibling (tail ++ skipped)) :=
        .settle started [] (tail ++ skipped) sibling pending (by simp [Scope.start])
      have ids := unique
      simp only [List.cons_append, List.map_cons, List.nodup_cons] at ids
      have freshLater : ∀ other ∈ tail ++ skipped,
          other.id ∉ ((scope.start sibling.id).settle [] sibling (tail ++ skipped)).started := by
        intro other present repeated
        simp only [Scope.settle, Scope.start, List.mem_append, List.mem_singleton] at repeated
        rcases repeated with old | same
        · exact fresh other (List.mem_cons_of_mem _ present) old
        · exact ids.1 (same ▸ List.mem_map_of_mem present)
      obtain ⟨final, valid, complete, settledAll, cancelled, actions⟩ :=
        ih settled rfl (by simp [Scope.settle, Scope.start, running, healthy]) ids.2 freshLater
      refine ⟨final, valid, complete, ?_, cancelled, ?_⟩
      · simpa only [Scope.settle, Scope.start, List.append_assoc, List.singleton_append]
          using settledAll
      · simpa only [Scope.settle, Scope.start, List.flatMap_cons, List.append_assoc,
          List.singleton_append, List.cons_append, List.nil_append] using actions

-----------------------------------------------------------------------------------------
-- The history uses this same actual eager plan, prefix completion and cut supply
-----------------------------------------------------------------------------------------

/-- Derive the original scope contract from the cut itself. No native history or
response-equivalence premise is supplied. IDs come from the actual observed eager plan.
-/
theorem ActionCut.scope_history {actions : List (StateM Nat (Completion α))}
    {supply completed remaining next}
    (cut : ActionCut actions supply completed remaining next) (id : Nat)
    : ∃ scope,
        History (completionPlan ((observeActions actions).run supply).1 id) scope
        ∧ scope.pending = []
        ∧ scope.settled = completionPlan completed id
        ∧ scope.cancelled
          = completionPlan ((observeActions remaining).run next).1 (id + completed.length)
        ∧ scope.actions
          = (completionPlan completed id).flatMap
              (fun sibling => [.start sibling.id, .settle sibling.id])
            ++ (completionPlan ((observeActions remaining).run next).1
                  (id + completed.length)).map
                (fun sibling => .cancel sibling.id)
        ∧ scope.reportedErrors
          = countedErrors (foldCompletions List.cons [] completed).result := by
  rw [cut.observed]
  dsimp only
  have shaped := cut.prefix id
  have unique := completionPlan_unique
    (completed ++ ((observeActions remaining).run next).1) id
  rw [completionPlan_append] at unique ⊢
  obtain ⟨scope, history, complete, settled, cancelled, actions⟩ := shaped.scope_history
    (History.initial (plan := completionPlan completed id
      ++ completionPlan ((observeActions remaining).run next).1 (id + completed.length)))
    rfl rfl unique (by simp)
  refine ⟨scope, history, complete, settled, cancelled, actions, ?_⟩
  rw [Scope.reportedErrors, settled]
  simpa only [List.nil_append]
    using (foldCompletions_errors List.cons [] completed id).symm

-----------------------------------------------------------------------------------------
-- Exact error-free/nonfatal agreement at actual public field and list call sites
-----------------------------------------------------------------------------------------

theorem SameData.fatal_eq {left right : Result α} (same : SameData left right)
    : isFatal left = isFatal right := by
  cases left <;> cases right <;> simp_all [SameData, isFatal]

/-- The original nonfatal result suffices: no assumptions on independently selected
prefix outcomes or a desired native schedule are needed. Nullable counts may be positive.
-/
theorem cutActions_nonfatal_exact (combine : α → β → β) (base : β)
    (actions : List (StateM Nat (Completion α))) (supply : Nat)
    (healthy
      : isFatal ((executeActions combine base actions).run supply).1.result = false)
    : (cutActions combine base actions).run supply
      = (executeActions combine base actions).run supply := by
  have cut := observeUntilFatal_cut actions supply
  have agreement := (cut.sameData combine base).fatal_eq
  have exactness := cut.nonfatal_exact combine base (agreement.trans healthy)
  simpa only [cutActions, Semantics.run_bind, StateT.run_pure, Semantics.id_pure_eq]
    using exactness.2.symm

theorem executeCollectedFields_cut_exact (schema : Schema)
    (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
    (parentType : Name) (source : ResolverValue ObjectRef) (fields : CollectedFieldsMap)
    (path : ResponsePath) (usages : List Nat) (context : DeferMap) (supply : Nat)
    (healthy
      : isFatal
          ((executeCollectedFields schema resolvers variables fuel parentType source
              fields path usages context).run
            supply).1.result
        = false)
    : (cutActions List.append []
        (fieldActions schema resolvers variables fuel parentType source fields path usages
          context)).run
        supply
      = (executeCollectedFields schema resolvers variables fuel parentType source fields
          path usages context).run
          supply := by
  rw [executeCollectedFields_actions] at healthy ⊢
  exact cutActions_nonfatal_exact _ _ _ _ healthy

theorem completeListValue_cut_exact (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues) (fuel : Nat) (itemType : TypeRef)
    (fields : List FieldDetails) (values : List (ResolverValue ObjectRef))
    (path : ResponsePath) (index : Nat) (usages : List Nat) (context : DeferMap)
    (supply : Nat)
    (healthy
      : isFatal
          ((completeListValue schema resolvers variables fuel itemType fields values path
              index usages context).run
            supply).1.result
        = false)
    : (cutActions List.cons []
        (listActions schema resolvers variables fuel itemType fields path usages context
          values index)).run
        supply
      = (completeListValue schema resolvers variables fuel itemType fields values path
          index usages context).run
          supply := by
  rw [completeListValue_actions] at healthy ⊢
  exact cutActions_nonfatal_exact _ _ _ _ healthy

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.ScheduledErrors
