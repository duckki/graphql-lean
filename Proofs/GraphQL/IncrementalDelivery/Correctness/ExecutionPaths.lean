import Proofs.GraphQL.IncrementalDelivery.Semantics.CollectionProperties
import Proofs.GraphQL.IncrementalDelivery.Correctness.WorkMetadata

/-! Generated work stays below the response attachment that produced it. -/

namespace GraphQL.IncrementalDelivery.Correctness.ExecutionPaths
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Semantics
open WorkQueueSemantics

variable {ObjectRef : Type}
attribute [local simp] id_pure_eq id_bind_eq id_map_eq run_bind run_map

-----------------------------------------------------------------------------------------
-- A structural path certificate, independent of observation and cancellation
-----------------------------------------------------------------------------------------

mutual
  /-- Each task attachment lies below `base`; child work lies below its own producer's
  attachment. Stream children use the list attachment, not the individual item coordinate.
  -/
  def WorkUnder (base : ResponsePath) : Work → Prop
    | .empty => True
    | .combine left right => WorkUnder base left ∧ WorkUnder base right
    | .executionGroup _ path _ children =>
        base.IsPrefix path ∧ WorkUnder path children
    | .stream node items => base.IsPrefix node.path ∧ ItemsUnder node.path items

  /-- Every streamed item's child work stays below the enclosing list's `base` path. -/
  def ItemsUnder (base : ResponsePath) : List (Result ResponseValue × Work) → Prop
    | [] => True
    | (_, children) :: rest => WorkUnder base children ∧ ItemsUnder base rest
end

/-- The retained work in `completed` stays below `base`. -/
def Under (base : ResponsePath) (completed : Completion α) : Prop :=
  WorkUnder base completed.work

/-- Moving the outer bound upward preserves the certificate. Witness: only the outer
task/list attachment changes its prefix obligation; producer-local bounds are retained.
-/
theorem WorkUnder.mono {base next work} (under : WorkUnder next work)
    (below : base.IsPrefix next)
    : WorkUnder base work := by
  cases work with
  | empty => trivial
  | combine left right =>
      exact ⟨WorkUnder.mono under.1 below, WorkUnder.mono under.2 below⟩
  | executionGroup => exact ⟨below.trans under.1, under.2⟩
  | stream => exact ⟨below.trans under.1, under.2⟩
termination_by work

/-- Moving a completion's outer bound upward preserves its retained work. -/
theorem Under.mono {base next} {completed : Completion α}
    (under : Under next completed) (below : base.IsPrefix next)
    : Under base completed :=
  WorkUnder.mono under below

/-- Pure and failed completions retain no work. Witness: their empty work constructor. -/
theorem pure (base : ResponsePath) (value : α) : Under base (Completion.pure value) :=
  trivial

/-- Failed completions retain no work, regardless of their error count. -/
theorem error (base : ResponsePath) (errors : Nat)
    : Under base (Completion.error errors : Completion α) :=
  trivial

/-- Combining completions either joins their certified work or discards it on failure.
-/
theorem combine (base : ResponsePath) (f : α → β → γ)
    (left : Completion α) (right : Completion β)
    (hl : Under base left) (hr : Under base right)
    : Under base (Completion.combine f left right) := by
  change WorkUnder base left.work at hl
  change WorkUnder base right.work at hr
  cases h : Result.combine f left.result right.result <;>
    simp [Under, Completion.combine, h, Completion.error, WorkUnder, hl, hr]

/-- Mapping successful values preserves work; mapping a failure retains no work. -/
theorem map (base : ResponsePath) (f : α → β) (completed : Completion α)
    (h : Under base completed)
    : Under base (Completion.map f completed) := by
  change WorkUnder base completed.work at h
  cases hresult : completed.result <;>
    simp [Under, Completion.map, hresult, Completion.error, WorkUnder, h]

/-- Null catching preserves successful work and discards bubbling work. -/
theorem catchNull (base : ResponsePath) (f : α → ResponseValue)
    (completed : Completion α) (h : Under base completed)
    : Under base (Completion.catchNull f completed) := by
  change WorkUnder base completed.work at h
  cases hresult : completed.result <;>
    simp [Under, Completion.catchNull, hresult, WorkUnder, h]

/-- Non-null completion either retains the same work or discards it on failure. -/
theorem nonNull (base : ResponsePath) (completed : Completion ResponseValue)
    (h : Under base completed)
    : Under base (Completion.nonNull completed) := by
  unfold Completion.nonNull
  split
  · exact error _ _
  · exact h

-----------------------------------------------------------------------------------------
-- Execution preserves attachment locality through every completion branch
-----------------------------------------------------------------------------------------

mutual
  /-- Plan execution keeps immediate work below its path and groups below their producer.
  Witness: mutual induction through collected fields and deferred partitions.
  -/
  theorem executePlan_under (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variables : VariableValues) (fuel : Nat) (parentType : Name)
      (source : ResolverValue ObjectRef) (collection : FieldCollection)
      (path : ResponsePath) (usages : NodeRefs) (deferMap : DeferMap)
      : RunEnsures (Under path)
          (executeExecutionPlan schema resolvers variables fuel parentType source
            collection.newDeferUsages
            (buildExecutionPlan collection.collectedFieldsMap usages) path usages
            deferMap) := by
    simp only [executeExecutionPlan]
    refine runEnsures_bind (Under path) _ _ _ ?_ ?_
    · exact executeCollectedFields_under schema resolvers variables fuel parentType source
        _ path usages _
    · intro completed hc
      split
      · exact runEnsures_pure _ _ hc
      · refine runEnsures_bind (WorkUnder path) _ _ _ ?_ ?_
        · exact collectExecutionGroups_under schema resolvers variables fuel parentType
            source _ path _
        · intro work hw
          exact runEnsures_pure _ _ ⟨hc, hw⟩
  termination_by (fuel, 6, 0, 0)
  decreasing_by
    all_goals simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right
    all_goals try omega

  /-- Each execution group uses the current path and certifies its own child work.
  Witness: partition-list induction and collected-field completion.
  -/
  theorem collectExecutionGroups_under (schema : Schema)
      (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
      (parentType : Name) (source : ResolverValue ObjectRef)
      (partitions : List (NodeRefs × CollectedFieldsMap)) (path : ResponsePath)
      (deferMap : DeferMap)
      : RunEnsures (WorkUnder path)
          (collectExecutionGroups schema resolvers variables fuel parentType source
            partitions path deferMap) := by
    cases partitions with
    | nil => simp [collectExecutionGroups, RunEnsures, WorkUnder]
    | cons partition rest =>
        rcases partition with ⟨usages, groups⟩
        simp only [collectExecutionGroups, executeExecutionGroup]
        refine runEnsures_bind (Under path) _ _ _ ?_ ?_
        · exact executeCollectedFields_under schema resolvers variables fuel parentType
            source groups path usages deferMap
        · intro completed hc
          refine runEnsures_bind (WorkUnder path) _ _ _ ?_ ?_
          · exact collectExecutionGroups_under schema resolvers variables fuel parentType
              source rest path deferMap
          · intro work hw
            exact runEnsures_pure _ _ ⟨⟨⟨[], by simp⟩, hc⟩, hw⟩
  termination_by (fuel, 5, 0, sizeOf partitions)
  decreasing_by
    all_goals subst_vars; simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right
    all_goals try omega

  /-- Collected fields keep all joined work below their enclosing response path.
  Witness: field-list induction and certified completion combination.
  -/
  theorem executeCollectedFields_under (schema : Schema)
      (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
      (parentType : Name) (source : ResolverValue ObjectRef) (groups : CollectedFieldsMap)
      (path : ResponsePath) (usages : NodeRefs) (deferMap : DeferMap)
      : RunEnsures (Under path)
          (executeCollectedFields schema resolvers variables fuel parentType source groups
            path usages deferMap) := by
    cases groups with
    | nil =>
        simpa only [executeCollectedFields_nil] using runEnsures_pure _ _ (pure path
          ([] : List (Name × ResponseValue)))
    | cons group rest =>
        rcases group with ⟨name, fields⟩
        simp only [executeCollectedFields_cons]
        refine runEnsures_bind (Under path) _ _ _ ?_ ?_
        · exact executeResponseField_under schema resolvers variables fuel parentType source
            name fields path usages deferMap
        · intro head hh
          refine runEnsures_bind (Under path) _ _ _ ?_ ?_
          · exact executeCollectedFields_under schema resolvers variables fuel parentType
              source rest path usages deferMap
          · intro tail ht
            exact runEnsures_pure _ _ (combine path List.append head tail hh ht)
  termination_by (fuel, 4, 0, sizeOf groups)
  decreasing_by
    all_goals subst_vars; simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right
    all_goals try omega

  /-- Field completion extends its enclosing path by the response name, never sideways.
  Witness: lookup/error cases and prefix weakening of the completed field's certificate.
  -/
  theorem executeResponseField_under (schema : Schema)
      (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
      (parentType : Name) (source : ResolverValue ObjectRef) (name : Name)
      (fields : List FieldDetails) (path : ResponsePath)
      (usages : NodeRefs) (deferMap : DeferMap)
      : RunEnsures (Under path)
          (executeResponseField schema resolvers variables fuel parentType source name
            fields path usages deferMap) := by
    cases fuel with
    | zero =>
        simpa only [executeResponseField] using runEnsures_pure _ _ (error path 1)
    | succ fuel =>
        cases fields with
        | nil =>
            simpa only [executeResponseField] using runEnsures_pure _ _ (error path 1)
        | cons field rest =>
            simp only [executeResponseField]
            split
            · exact runEnsures_pure _ _ (error path 1)
            · split
              · exact runEnsures_pure _ _ (show Under path _ from trivial)
              · split
                · exact runEnsures_pure _ _ (show Under path _ from trivial)
                · refine runEnsures_bind (Under (path ++ [.field name])) _ _ _ ?_ ?_
                  · exact completeValue_under schema resolvers variables fuel _ _ _
                      (path ++ [.field name]) usages deferMap true
                  · intro completed hc
                    exact runEnsures_pure _ _ (map path _ completed
                      (hc.mono ⟨[.field name], rfl⟩))
  termination_by (fuel, 3, 0, sizeOf fields)
  decreasing_by
    all_goals subst_vars; simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right
    all_goals try omega

  /-- Value completion retains only work below the value's attachment.
  Witness: mutual induction on fuel, type wrappers, object plans, and list completion.
  -/
  theorem completeValue_under (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variables : VariableValues) (fuel : Nat) (fieldType : TypeRef)
      (fields : List FieldDetails) (value : ResolverValue ObjectRef)
      (path : ResponsePath) (usages : NodeRefs) (deferMap : DeferMap) (allowStream : Bool)
      : RunEnsures (Under path)
          (completeValue schema resolvers variables fuel fieldType fields value path
            usages deferMap allowStream) := by
    cases fuel with
    | zero =>
        simpa only [completeValue] using runEnsures_pure _ _ (error path 1)
    | succ fuel =>
        cases fieldType with
        | nonNull inner =>
            simp only [completeValue]
            refine runEnsures_bind (Under path) _ _ _ ?_ ?_
            · exact completeValue_under schema resolvers variables (fuel + 1) inner fields
                value path usages deferMap allowStream
            · intro completed hc
              exact runEnsures_pure _ _ (nonNull path completed hc)
        | named parentType =>
            cases value with
            | null =>
                simpa only [completeValue] using runEnsures_pure _ _
                  (pure path ResponseValue.null)
            | scalar scalar =>
                simp only [completeValue]
                split
                · exact runEnsures_pure _ _ (error path 1)
                · exact runEnsures_pure _ _ (pure path _)
            | list items =>
                simpa only [completeValue] using runEnsures_pure _ _ (error path 1)
            | object runtimeType ref =>
                simp only [completeValue]
                split
                · exact runEnsures_pure _ _ (error path 1)
                · refine runEnsures_bind (fun _ : FieldCollection => True) _ _ _
                    (fun _ => trivial) ?_
                  intro collection _
                  refine runEnsures_bind (Under path) _ _ _ ?_ ?_
                  · exact executePlan_under schema resolvers variables fuel runtimeType
                      (.object runtimeType ref) collection path usages deferMap
                  · intro completed hc
                    exact runEnsures_pure _ _ (catchNull path _ completed hc)
        | list inner =>
            cases value with
            | null =>
                simpa only [completeValue] using runEnsures_pure _ _
                  (pure path ResponseValue.null)
            | scalar scalar =>
                simpa only [completeValue] using runEnsures_pure _ _ (error path 1)
            | object runtimeType ref =>
                simpa only [completeValue] using runEnsures_pure _ _ (error path 1)
            | list items =>
                simpa only [completeValue] using completeListValueWithStream_under
                  schema resolvers variables fuel inner fields items path usages deferMap
                  allowStream
  termination_by (fuel, 1, sizeOf fieldType, 0)
  decreasing_by
    all_goals subst_vars; simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right
    all_goals try omega

  /-- The stream hook attaches retained tails at the list's path, including empty tails.
  Witness: initial-list completion and certified stream-item children.
  -/
  theorem completeListValueWithStream_under (schema : Schema)
      (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
      (inner : TypeRef) (fields : List FieldDetails)
      (values : List (ResolverValue ObjectRef)) (path : ResponsePath)
      (usages : NodeRefs) (deferMap : DeferMap) (allowStream : Bool)
      : RunEnsures (Under path)
          (completeListValueWithStream schema resolvers variables fuel inner fields
            values path usages deferMap allowStream) := by
    unfold completeListValueWithStream
    dsimp only
    split
    · exact runEnsures_pure _ _ trivial
    · refine runEnsures_bind (Under path) _ _ _ ?_ ?_
      · exact completeListValue_under schema resolvers variables fuel inner fields
          values path 0 usages deferMap
      · intro completed hc
        exact runEnsures_pure _ _ (catchNull path _ completed hc)
    · rename_i usage _
      refine runEnsures_bind (Under path) _ _ _ ?_ ?_
      · exact completeListValue_under schema resolvers variables fuel inner fields
          (values.take usage.initialCount) path 0 usages deferMap
      · intro initial hi
        split
        · exact runEnsures_pure _ _ (catchNull path _ initial hi)
        · split
          · exact runEnsures_pure _ _ (catchNull path _ initial hi)
          · refine runEnsures_bind (fun _ : NodeRef => True) _ _ _ (fun _ => trivial) ?_
            intro ref _
            refine runEnsures_bind (ItemsUnder path)
              _ _ _ ?_ ?_
            · exact completeStreamItems_under schema resolvers variables fuel inner
                _ _ path usage.initialCount
            · intro tail ht
              exact runEnsures_pure _ _
                ⟨catchNull path _ initial hi, ⟨[], by simp⟩, ht⟩
  termination_by (fuel, 3, 0, 0)
  decreasing_by
    all_goals subst_vars; simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right

  /-- Ordinary list completion keeps indexed-item work below the enclosing list.
  Witness: item-list induction and weakening from the extended index path.
  -/
  theorem completeListValue_under (schema : Schema)
      (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
      (itemType : TypeRef) (fields : List FieldDetails)
      (values : List (ResolverValue ObjectRef)) (path : ResponsePath) (index : Nat)
      (usages : NodeRefs) (deferMap : DeferMap)
      : RunEnsures (Under path)
          (completeListValue schema resolvers variables fuel itemType fields values path
            index usages deferMap) := by
    cases values with
    | nil =>
        simpa only [completeListValue] using runEnsures_pure _ _
          (pure path ([] : List ResponseValue))
    | cons value rest =>
        simp only [completeListValue]
        refine runEnsures_bind (Under (path ++ [.index index])) _ _ _ ?_ ?_
        · exact completeValue_under schema resolvers variables fuel itemType fields value
            (path ++ [.index index]) usages deferMap false
        · intro head hh
          refine runEnsures_bind (Under path) _ _ _ ?_ ?_
          · exact completeListValue_under schema resolvers variables fuel itemType fields
              rest path (index + 1) usages deferMap
          · intro tail ht
            exact runEnsures_pure _ _ (combine path List.cons head tail
              (hh.mono ⟨[.index index], rfl⟩) ht)
  termination_by (fuel, 2, sizeOf itemType, sizeOf values)
  decreasing_by
    all_goals subst_vars; simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right
    all_goals try omega

  /-- Every streamed item's child work stays below its list attachment.
  Witness: early-stop failure retains no children; successful items extend the list path.
  -/
  theorem completeStreamItems_under (schema : Schema)
      (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
      (itemType : TypeRef) (fields : List FieldDetails)
      (values : List (ResolverValue ObjectRef)) (path : ResponsePath) (index : Nat)
      : RunEnsures (ItemsUnder path)
          (completeStreamItems schema resolvers variables fuel itemType fields values
            path index) := by
    cases values with
    | nil => simp [completeStreamItems, RunEnsures, ItemsUnder]
    | cons value rest =>
        simp only [completeStreamItems]
        refine runEnsures_bind (Under (path ++ [.index index])) _ _ _ ?_ ?_
        · exact completeValue_under schema resolvers variables fuel itemType fields value
            (path ++ [.index index]) [] [] false
        · intro head hh
          split
          · exact runEnsures_pure _ _ ⟨trivial, trivial⟩
          · refine runEnsures_bind (ItemsUnder path)
              _ _ _ ?_ ?_
            · exact completeStreamItems_under schema resolvers variables fuel itemType
                fields rest path (index + 1)
            · intro tail ht
              exact runEnsures_pure _ _ ⟨hh.mono ⟨[.index index], rfl⟩, ht⟩
  termination_by (fuel, 2, sizeOf itemType, sizeOf values)
  decreasing_by
    all_goals subst_vars; simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right
    all_goals omega
end

/-- Root execution certifies every producer-local attachment bound.
Witness: root collection and the mutually proved plan certificate, with outer path `[]`.
-/
theorem executeRootSelectionSetCore_under (schema : Schema)
    (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
    (parentType : Name) (source : ResolverValue ObjectRef) (selections : List Selection)
    : RunEnsures (Under [])
        (executeRootSelectionSetCore schema resolvers variables fuel parentType source
          selections) := by
  simp only [executeRootSelectionSetCore]
  refine runEnsures_bind (fun _ : FieldCollection => True) _ _ _ (fun _ => trivial) ?_
  intro collection _
  exact executePlan_under schema resolvers variables fuel parentType source collection
    [] [] []

end GraphQL.IncrementalDelivery.Correctness.ExecutionPaths
