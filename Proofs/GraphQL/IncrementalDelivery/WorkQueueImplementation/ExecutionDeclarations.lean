import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.WorkDeclarations
import Proofs.GraphQL.IncrementalDelivery.Semantics.AncestryMetadata
import Proofs.GraphQL.IncrementalDelivery.Semantics.CollectionProperties
import Proofs.GraphQL.IncrementalDelivery.Semantics.SingleStreamCompletion

/-! Execution-derived registration contexts for explicit group declarations. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue.DeclarationCoverage
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Semantics
open Semantics.Ancestry (mapRefs)
open WorkQueueSemantics (NodeRefs)

/-- Execution maps retain every ancestor named by their fragments. -/
class ClosedMap (deferMap : DeferMap) : Prop where
  ancestors
    : ∀ fragment ∈ deferMap,
      ∀ ancestor ∈ fragment.ancestors, ancestor.ref ∈ mapRefs deferMap

instance : ClosedMap [] := ⟨by intro fragment member; cases member⟩

/-- Fresh fragment ancestors are looked up in the preceding map. -/
theorem closedMap_getNewDeferMap (usages : List DeferUsage) (path : ResponsePath)
    (old : DeferMap) (closed : ClosedMap old)
    : ClosedMap (getNewDeferMap usages path old) := by
  induction usages generalizing old with
  | nil => simpa only [getNewDeferMap, List.foldl_nil] using closed
  | cons usage rest ih =>
      rw [getNewDeferMap, List.foldl_cons]
      apply ih
      constructor
      intro fragment member ancestor selected
      simp only [mapRefs, List.map_append]
      rcases List.mem_append.mp member with earlier | fresh
      · exact List.mem_append_left _ (closed.ancestors fragment earlier ancestor selected)
      · obtain rfl := List.mem_singleton.mp fresh
        obtain ⟨ref, _, found⟩ := List.mem_filterMap.mp selected
        obtain ⟨prior, lookup, same⟩ := Option.map_eq_some_iff.mp found
        subst ancestor
        exact List.mem_append_left _
          (List.mem_map.mpr ⟨prior, List.mem_of_find?_eq_some lookup, rfl⟩)

instance (usages : List DeferUsage) (path : ResponsePath) (old : DeferMap)
    [closed : ClosedMap old]
    : ClosedMap (getNewDeferMap usages path old) :=
  closedMap_getNewDeferMap usages path old closed

/-- Immediate fresh declarations; deferred and item children have later integration cuts. -/
def declarations : Execution.Work → NodeRefs
  | .empty => []
  | .combine left right => declarations left ++ declarations right
  | .declareGroups groups tasks => mapRefs groups ++ declarations tasks
  | .executionGroup _ _ _ _ | .stream _ _ => []

/-- Every task uses previously declared refs or declarations integrated with this chunk.
Sibling declarations are registered before either sibling's tasks. Stream items restart
with an empty defer context. Deferred children retain the chunk's declaration context.
-/
def Certified (known : NodeRefs) : Execution.Work → Prop
  | .empty => True
  | .combine left right =>
      Certified (known ++ declarations right) left
      ∧ Certified (known ++ declarations left) right
  | .declareGroups groups tasks =>
      (∀ fragment ∈ groups,
        ∀ parent,
          fragment.ancestors.head?.map DeliveryNode.ref = some parent
          → parent ∈ known ++ mapRefs groups)
      ∧ Certified (known ++ mapRefs groups) tasks
  | .executionGroup groups _ _ children =>
      (mapRefs groups).Subset known ∧ Certified known children
  | .stream _ items => ∀ entry ∈ items, Certified [] entry.2
termination_by work => sizeOf work
decreasing_by
  all_goals subst_vars; simp_wf
  all_goals try decreasing_trivial
  have smaller := List.sizeOf_lt_of_mem ‹entry ∈ items›
  rcases entry with ⟨result, children⟩
  simp only [Prod.mk.sizeOf_spec] at smaller
  dsimp only
  omega

private theorem append_subset {left right : NodeRefs} (known : left.Subset right)
    (extra : NodeRefs)
    : (left ++ extra).Subset (right ++ extra) := by
  intro ref member
  rcases List.mem_append.mp member with earlier | later
  · exact List.mem_append_left _ (known earlier)
  · exact List.mem_append_right _ later

/-- Widening a declaration context preserves the certificate. -/
theorem Certified.mono {known more work} (certified : Certified known work)
    (included : known.Subset more)
    : Certified more work := by
  cases work with
  | empty => simp only [Certified]
  | combine left right =>
      rw [Certified] at certified ⊢
      constructor
      · exact certified.1.mono (append_subset included _)
      · exact certified.2.mono (append_subset included _)
  | declareGroups groups tasks =>
      rw [Certified] at certified ⊢
      exact ⟨fun fragment member parent present =>
        append_subset included _ (certified.1 fragment member parent present),
        certified.2.mono (append_subset included _)⟩
  | executionGroup groups path result children =>
      rw [Certified] at certified ⊢
      exact ⟨certified.1.trans included, certified.2.mono included⟩
  | stream node items => simpa only [Certified] using certified
termination_by work

/-- Independent certified components may be integrated together. -/
theorem Certified.combine {known left right} (leftKnown : Certified known left)
    (rightKnown : Certified known right)
    : Certified known (.combine left right) := by
  rw [Certified]
  exact ⟨leftKnown.mono (List.subset_append_left _ _),
    rightKnown.mono (List.subset_append_left _ _)⟩

/-- Retained work uses the declared context; bubbling completions discard all work. -/
def Completed (known : NodeRefs) (completed : Completion α) : Prop :=
  Certified known completed.work
  ∧ ∀ errors, completed.result = .error errors → completed.work = .empty

/-- A pure completion introduces no tasks. -/
theorem pure (known : NodeRefs) (value : α)
    : Completed known (Completion.pure value) := by
  simp [Completed, Completion.pure, Certified]

/-- An immediate error retains no work. -/
theorem error (known : NodeRefs) (errors : Nat)
    : Completed known (Completion.error errors : Completion α) := by
  simp [Completed, Completion.error, Certified]

/-- Successful combination integrates both components; bubbling discards all work. -/
theorem combine (f : α → β → γ) (left : Completion α) (right : Completion β)
    {known} (hl : Completed known left) (hr : Completed known right)
    : Completed known (Completion.combine f left right) := by
  cases he : Result.combine f left.result right.result with
  | error errors => simp [Completed, Completion.combine, he, Completion.error, Certified]
  | ok result =>
      refine ⟨?_, ?_⟩
      · simpa only [Completion.combine, he] using hl.1.combine hr.1
      · simp [Completion.combine, he]

/-- Response mapping preserves retained work, or discards it on failure. -/
theorem map (f : α → β) (completed : Completion α) {known} (h : Completed known completed)
    : Completed known (Completion.map f completed) := by
  cases he : completed.result with
  | error errors => simp [Completed, Completion.map, he, Completion.error, Certified]
  | ok result =>
      refine ⟨?_, ?_⟩
      · simpa only [Completion.map, he] using h.1
      · simp [Completion.map, he]

/-- Nullable catching retains successful work and clears work on failure. -/
theorem catchNull (f : α → ResponseValue) (completed : Completion α) {known}
    (h : Completed known completed)
    : Completed known (Completion.catchNull f completed) := by
  cases he : completed.result with
  | error errors => simp [Completed, Completion.catchNull, he, Certified]
  | ok result =>
      refine ⟨?_, ?_⟩
      · simpa only [Completion.catchNull, he] using h.1
      · simp [Completion.catchNull, he]

/-- Non-null completion retains successful work and clears work on failure. -/
theorem nonNull (completed : Completion ResponseValue) {known}
    (h : Completed known completed)
    : Completed known (Completion.nonNull completed) := by
  cases he : nonNullCompletion completed.result with
  | error errors => simp [Completed, Completion.nonNull, he, Completion.error, Certified]
  | ok result =>
      refine ⟨?_, ?_⟩
      · simpa only [Completion.nonNull, he] using h.1
      · simp [Completion.nonNull, he]

/-- Each streamed item's retained work starts with no inherited defer declarations. -/
def ItemsCertified : List (TaskOutcome ResponseValue × Execution.Work) → Prop
  | [] => True
  | (_, children) :: rest => Certified [] children ∧ ItemsCertified rest

/-- Each item entry inherits its finite list certificate. -/
theorem ItemsCertified.member {items} (known : ItemsCertified items) {entry}
    (member : entry ∈ items)
    : Certified [] entry.2 := by
  induction items with
  | nil => cases member
  | cons first rest ih =>
      rcases List.mem_cons.mp member with same | later
      · exact same ▸ known.1
      · exact ih known.2 later

/-- Every newly appended map ref is present in the explicit declaration inventory. -/
theorem map_refs_declared (usages : List DeferUsage) (path : ResponsePath)
    (old : DeferMap)
    : (mapRefs (getNewDeferMap usages path old)).Subset
        (mapRefs old
          ++ mapRefs
              (usages.filterMap
                (fun usage =>
                  lookupDeferredFragment? (getNewDeferMap usages path old)
                    usage.ref))) := by
  intro ref member
  rw [Semantics.Ancestry.getNewDeferMap_refs] at member
  rcases List.mem_append.mp member with earlier | fresh
  · exact List.mem_append_left _ earlier
  · obtain ⟨usage, included, same⟩ := List.mem_map.mp fresh
    have present : usage.ref ∈ mapRefs (getNewDeferMap usages path old) := by
      rw [Semantics.Ancestry.getNewDeferMap_refs]
      exact List.mem_append_right _ (List.mem_map_of_mem included)
    obtain ⟨fragment, found⟩ := Semantics.Ancestry.lookup_exists present
    apply List.mem_append_right
    apply List.mem_map.mpr
    refine ⟨fragment, List.mem_filterMap.mpr ⟨usage, included, found⟩, ?_⟩
    exact (Semantics.Ancestry.lookup_ref found).trans same

/-- Plan declarations establish the extended map before either component's tasks start. -/
theorem planWork (usages : List DeferUsage) (path : ResponsePath) (old : DeferMap)
    [ClosedMap old] {initial tasks : Execution.Work}
    (hi : Certified (mapRefs (getNewDeferMap usages path old)) initial)
    (ht : Certified (mapRefs (getNewDeferMap usages path old)) tasks)
    : Certified (mapRefs old)
        (.combine initial
          (.declareGroups
            (usages.filterMap
              (fun usage =>
                lookupDeferredFragment? (getNewDeferMap usages path old) usage.ref))
            tasks)) := by
  have context := map_refs_declared usages path old
  rw [Certified]
  constructor
  · apply hi.mono
    intro ref member
    rcases List.mem_append.mp (context member) with earlier | freshRef
    · exact List.mem_append_left _ earlier
    · exact List.mem_append_right _ (List.mem_append_left _ freshRef)
  · rw [Certified]
    constructor
    · intro fragment member parent present
      obtain ⟨usage, _, found⟩ := List.mem_filterMap.mp member
      obtain ⟨ancestor, selected, same⟩ := Option.map_eq_some_iff.mp present
      have included := List.mem_of_find?_eq_some found
      have ancestorMember := List.mem_of_mem_head? selected
      have parentKnown := ClosedMap.ancestors fragment included ancestor ancestorMember
      have extended := context parentKnown
      rw [← same]
      exact List.mem_append.mpr ((List.mem_append.mp extended).elim
        (fun prior => Or.inl (List.mem_append_left _ prior)) Or.inr)
    apply ht.mono
    intro ref member
    rcases List.mem_append.mp (context member) with earlier | freshRef
    · exact List.mem_append_left _ (List.mem_append_left _ earlier)
    · exact List.mem_append_right _ freshRef

/-- Every looked-up task owner is already present in its execution map. -/
theorem deferred (deferMap : DeferMap) (usages : NodeRefs) (path : ResponsePath)
    (result : TaskOutcome (List (Name × ResponseValue))) {children : Execution.Work}
    (known : Certified (mapRefs deferMap) children)
    : Certified (mapRefs deferMap)
        (.executionGroup (usages.filterMap (lookupDeferredFragment? deferMap)) path result
          children) := by
  rw [Certified]
  refine ⟨?_, known⟩
  intro ref member
  obtain ⟨fragment, included, rfl⟩ := List.mem_map.mp member
  obtain ⟨usage, _, found⟩ := List.mem_filterMap.mp included
  exact List.mem_map_of_mem (List.mem_of_find?_eq_some found)

/-- An immediate field error retains no work, regardless of its nullability. -/
theorem failedField (known : NodeRefs) (name : Name) (fieldType : TypeRef)
    : Completed known
        ({
            result :=
              GraphQL.Execution.singleFieldResult name
                (GraphQL.Execution.handleFieldError fieldType)
            cause := if fieldType.isNonNull then some 1 else none
          }
          : Completion _) := by
  simp only [Completed, Certified, and_self, implies_true]

variable {ObjectRef : Type}
attribute [local simp] id_pure_eq id_bind_eq id_map_eq run_bind run_map

mutual
  /-- Plan execution retains certified immediate and deferred declarations, by mutual induction.
  -/
  theorem executePlan_declarations (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variables : VariableValues) (fuel : Nat) (parentType : Name)
      (source : ResolverValue ObjectRef)
      (collection : FieldCollection)
      (path : ResponsePath) (usages : List Nat) (deferMap : DeferMap)
      [ClosedMap deferMap]
      : RunEnsures (Completed (mapRefs deferMap))
          (executeExecutionPlan schema resolvers variables fuel parentType source
            collection.newDeferUsages
            (buildExecutionPlan collection.collectedFieldsMap usages) path usages
            deferMap) := by
    simp only [executeExecutionPlan]
    refine runEnsures_bind
      (Completed (mapRefs (getNewDeferMap collection.newDeferUsages path deferMap))) _ _ _
      ?_ ?_
    · exact executeCollectedFields_declarations schema resolvers variables fuel parentType source
        _ path usages _
    · intro completed hc
      split
      · apply runEnsures_pure
        -- A bubbling plan returns no retained work.
        rename_i errors failed
        have cleared := hc.2 errors failed
        exact ⟨by simp only [cleared, Certified], fun _ _ => cleared⟩
      · refine runEnsures_bind (Certified (mapRefs (getNewDeferMap collection.newDeferUsages path deferMap))) _ _ _ ?_ ?_
        · exact collectExecutionGroups_declarations schema resolvers variables fuel parentType
            source _ path _
        · intro work hw
          apply runEnsures_pure
          refine ⟨planWork _ _ _ hc.1 hw, ?_⟩
          intro errors failed
          rename_i value succeeded
          simp only [succeeded, reduceCtorEq] at failed
  termination_by (fuel, 6, 0, 0)
  decreasing_by
    all_goals
      simp_wf
      repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right
      try omega

  /-- Every deferred group and its children retain declaration coverage, by group-list induction. -/

  theorem collectExecutionGroups_declarations (schema : Schema)
      (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
      (parentType : Name) (source : ResolverValue ObjectRef)
      (partitions : List (List Nat × CollectedFieldsMap))
      (path : ResponsePath)
      (deferMap : DeferMap)
      [ClosedMap deferMap]
      : RunEnsures (Certified (mapRefs deferMap))
          (collectExecutionGroups schema resolvers variables fuel parentType source
            partitions path deferMap) := by
    cases partitions with
    | nil => simp [collectExecutionGroups, RunEnsures, Certified]
    | cons partition rest =>
        rcases partition with ⟨usages, groups⟩
        simp only [collectExecutionGroups, executeExecutionGroup]
        refine runEnsures_bind (Completed (mapRefs deferMap)) _ _ _ ?_ ?_
        · exact executeCollectedFields_declarations schema resolvers variables fuel parentType
            source groups path usages deferMap
        · intro completed hc
          refine runEnsures_bind (Certified (mapRefs deferMap)) _ _ _ ?_ ?_
          · exact collectExecutionGroups_declarations schema resolvers variables fuel parentType
              source rest path deferMap
          · intro work hw
            exact runEnsures_pure _ _ ((deferred deferMap usages path _ hc.1).combine hw)
  termination_by (fuel, 5, 0, sizeOf partitions)
  decreasing_by
    all_goals
      subst_vars
      simp_wf
      repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right
      try omega

  /-- Collected fields preserve declaration coverage when combined, by field-list induction. -/

  theorem executeCollectedFields_declarations (schema : Schema)
      (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
      (parentType : Name) (source : ResolverValue ObjectRef) (groups : CollectedFieldsMap)
      (path : ResponsePath) (usages : List Nat)
      (deferMap : DeferMap)
      [ClosedMap deferMap]
      : RunEnsures (Completed (mapRefs deferMap))
          (executeCollectedFields schema resolvers variables fuel parentType source groups
            path usages deferMap) := by
    cases groups with
    | nil =>
        simpa only [executeCollectedFields_nil] using runEnsures_pure _ _ (pure _ ([] : List
          (Name × ResponseValue)))
    | cons group rest =>
        rcases group with ⟨name, fields⟩
        simp only [executeCollectedFields_cons]
        refine runEnsures_bind (Completed (mapRefs deferMap)) _ _ _ ?_ ?_
        · exact executeResponseField_declarations schema resolvers variables fuel parentType source name
            fields path usages deferMap
        · intro head hh
          refine runEnsures_bind (Completed (mapRefs deferMap)) _ _ _ ?_ ?_
          · exact executeCollectedFields_declarations schema resolvers variables fuel parentType
              source rest path usages deferMap
          · intro tail ht
            exact runEnsures_pure _ _ (combine List.append head tail hh ht)
  termination_by (fuel, 4, 0, sizeOf groups)
  decreasing_by
    all_goals
      subst_vars
      simp_wf
      repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right
      try omega

  /-- Field completion retains its map context through resolver and nullability branches. -/

  theorem executeResponseField_declarations (schema : Schema)
      (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
      (parentType : Name) (source : ResolverValue ObjectRef) (name : Name)
      (fields : List FieldDetails) (path : ResponsePath)
      (usages : List Nat) (deferMap : DeferMap)
      [ClosedMap deferMap]
      : RunEnsures (Completed (mapRefs deferMap))
          (executeResponseField schema resolvers variables fuel parentType source name
            fields path usages deferMap) := by
    cases fuel with
    | zero =>
        simpa only [executeResponseField]
          using runEnsures_pure _ _ (error (α := List (Name × ResponseValue)) _ 1)
    | succ fuel =>
        cases fields with
        | nil =>
            simpa only [executeResponseField]
              using runEnsures_pure _ _ (error (α := List (Name × ResponseValue)) _ 1)
        | cons field rest =>
            simp only [executeResponseField]
            split
            · exact runEnsures_pure _ _ (error _ 1)
            · split
              · exact runEnsures_pure _ _ (failedField _ _ _)
              · split
                · exact runEnsures_pure _ _ (failedField _ _ _)
                · refine runEnsures_bind (Completed (mapRefs deferMap)) _ _ _ ?_ ?_
                  · exact completeValue_declarations schema resolvers variables fuel _ _ _
                      (path ++ [.field name]) usages deferMap true
                  · intro completed hc
                    exact runEnsures_pure _ _ (map _ completed hc)
  termination_by (fuel, 3, 0, sizeOf fields)
  decreasing_by
    all_goals
      subst_vars
      simp_wf
      repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right
      try omega

  /-- Object completion registers fresh declarations; scalar and error branches retain no work. -/

  theorem completeValue_declarations (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variables : VariableValues) (fuel : Nat) (fieldType : TypeRef)
      (fields : List FieldDetails) (value : ResolverValue ObjectRef)
      (path : ResponsePath) (usages : List Nat)
      (deferMap : DeferMap) (allowStream : Bool)
      [ClosedMap deferMap]
      : RunEnsures (Completed (mapRefs deferMap))
          (completeValue schema resolvers variables fuel fieldType fields value path
            usages deferMap allowStream) := by
    cases fuel with
    | zero =>
        simpa only [completeValue]
          using runEnsures_pure _ _ (error (α := ResponseValue) _ 1)
    | succ fuel =>
        cases fieldType with
        | nonNull inner =>
            simp only [completeValue]
            refine runEnsures_bind (Completed (mapRefs deferMap)) _ _ _ ?_ ?_
            · exact completeValue_declarations schema resolvers variables (fuel + 1) inner fields
                value path usages deferMap allowStream
            · intro completed hc
              exact runEnsures_pure _ _ (nonNull completed hc)
        | named parentType =>
            cases value with
            | null =>
                simpa only [completeValue] using runEnsures_pure _ _ (pure _ ResponseValue.null)
            | scalar scalar =>
                simp only [completeValue]
                split
                · exact runEnsures_pure _ _ (error _ 1)
                · exact runEnsures_pure _ _ (pure _ _)
            | list items =>
                simpa only [completeValue]
                  using runEnsures_pure _ _ (error (α := ResponseValue) _ 1)
            | object runtimeType ref =>
                simp only [completeValue]
                split
                · exact runEnsures_pure _ _ (error _ 1)
                · refine runEnsures_bind (fun _ : FieldCollection => True) _ _ _
                    (fun _ => trivial) ?_
                  intro collection _
                  refine runEnsures_bind (Completed (mapRefs deferMap)) _ _ _ ?_ ?_
                  · exact executePlan_declarations schema resolvers variables fuel runtimeType
                      (.object runtimeType ref) collection path usages deferMap
                  · intro completed hv
                    exact runEnsures_pure _ _ (catchNull _ completed hv)
        | list inner =>
            cases value with
            | null =>
                simpa only [completeValue] using runEnsures_pure _ _ (pure _ ResponseValue.null)
            | scalar scalar =>
                simpa only [completeValue]
                  using runEnsures_pure _ _ (error (α := ResponseValue) _ 1)
            | object runtimeType ref =>
                simpa only [completeValue]
                  using runEnsures_pure _ _ (error (α := ResponseValue) _ 1)
            | list items =>
                simpa only [completeValue] using completeListValueWithStream_declarations
                  schema resolvers variables fuel inner fields items path usages deferMap
                  allowStream
  termination_by (fuel, 1, sizeOf fieldType, 0)
  decreasing_by
    all_goals
      subst_vars
      simp_wf
      repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right
      try omega

  /-- The stream hook preserves declaration coverage in both the initial prefix and tail;
  witness: ordinary completion and item-tail certificates.
  -/
  theorem completeListValueWithStream_declarations (schema : Schema)
      (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
      (inner : TypeRef) (fields : List FieldDetails)
      (values : List (ResolverValue ObjectRef)) (path : ResponsePath)
      (usages : List Nat) (deferMap : DeferMap) (allowStream : Bool)
      [ClosedMap deferMap]
      : RunEnsures (Completed (mapRefs deferMap))
          (completeListValueWithStream schema resolvers variables fuel inner fields
            values path usages deferMap allowStream) := by
    unfold completeListValueWithStream
    dsimp only
    split
    · exact runEnsures_pure _ _ (by simp [Completed, Certified])
    · refine runEnsures_bind (Completed (mapRefs deferMap)) _ _ _ ?_ ?_
      · exact completeListValue_declarations schema resolvers variables fuel inner fields
          values path 0 usages deferMap
      · intro completed hc
        exact runEnsures_pure _ _ (catchNull _ completed hc)
    · rename_i usage _
      refine runEnsures_bind (Completed (mapRefs deferMap)) _ _ _ ?_ ?_
      · exact completeListValue_declarations schema resolvers variables fuel inner fields
          (values.take usage.initialCount) path 0 usages deferMap
      · intro initial hi
        split
        · exact runEnsures_pure _ _ (catchNull _ initial hi)
        · split
          · exact runEnsures_pure _ _ (catchNull _ initial hi)
          · refine runEnsures_bind (fun _ : Nat => True) _ _ _ (fun _ => trivial) ?_
            intro ref _
            refine runEnsures_bind ItemsCertified _ _ _ ?_ ?_
            · exact completeStreamItems_declarations schema resolvers variables fuel inner
                _ _ path usage.initialCount
            · intro tail ht
              apply runEnsures_pure
              refine ⟨?_, ?_⟩
              · exact (catchNull _ initial hi).1.combine (by
                  rw [Certified]
                  exact fun entry member => ht.member member)
              · cases observed : initial.result <;> simp [Completion.catchNull, observed]
  termination_by (fuel, 3, 0, 0)
  decreasing_by
    all_goals subst_vars; simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right

  /-- Ordinary list items share the enclosing declaration context. -/

  theorem completeListValue_declarations (schema : Schema)
      (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
      (itemType : TypeRef) (fields : List FieldDetails)
      (values : List (ResolverValue ObjectRef))
      (path : ResponsePath) (index : Nat) (usages : List Nat) (deferMap : DeferMap)
      [ClosedMap deferMap]
      : RunEnsures (Completed (mapRefs deferMap))
          (completeListValue schema resolvers variables fuel itemType fields values path
            index usages deferMap) := by
    cases values with
    | nil =>
        simpa only [completeListValue] using runEnsures_pure _ _ (pure _ ([] : List ResponseValue))
    | cons value rest =>
        simp only [completeListValue]
        refine runEnsures_bind (Completed (mapRefs deferMap)) _ _ _ ?_ ?_
        · exact completeValue_declarations schema resolvers variables fuel itemType fields value
            (path ++ [.index index]) usages deferMap false
        · intro head hh
          refine runEnsures_bind (Completed (mapRefs deferMap)) _ _ _ ?_ ?_
          · exact completeListValue_declarations schema resolvers variables fuel itemType fields
              rest path (index + 1) usages deferMap
          · intro tail ht
            exact runEnsures_pure _ _ (combine List.cons head tail hh ht)
  termination_by (fuel, 2, sizeOf itemType, sizeOf values)
  decreasing_by
    all_goals
      subst_vars
      simp_wf
      repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right
      try omega

  /-- Stream tails retain independently certified child work; witness: the early-stop branch of completeStreamItems.
  -/
  theorem completeStreamItems_declarations (schema : Schema)
      (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
      (itemType : TypeRef) (fields : List FieldDetails)
      (values : List (ResolverValue ObjectRef)) (path : ResponsePath) (index : Nat)
      : RunEnsures ItemsCertified
          (completeStreamItems schema resolvers variables fuel itemType fields values
            path index) := by
    cases values with
    | nil => simp [completeStreamItems, RunEnsures, ItemsCertified]
    | cons value rest =>
        simp only [completeStreamItems]
        refine runEnsures_bind (Completed []) _ _ _ ?_ ?_
        · exact completeValue_declarations schema resolvers variables fuel itemType fields
            value (path ++ [.index index]) [] [] false
        · intro head hh
          split
          · rename_i errors he
            exact runEnsures_pure _ _ ⟨by simp [Certified], trivial⟩
          · refine runEnsures_bind ItemsCertified _ _ _ ?_ ?_
            · exact completeStreamItems_declarations schema resolvers variables fuel itemType
                fields rest path (index + 1)
            · intro tail ht
              exact runEnsures_pure _ _ ⟨hh.1, ht⟩
  termination_by (fuel, 2, sizeOf itemType, sizeOf values)
  decreasing_by
    all_goals subst_vars; simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right
    all_goals omega

end

/-- Root execution starts with no inherited declarations and certifies all retained work. -/
theorem executeRoot_declarations (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues) (fuel : Nat) (parentType : Name)
    (source : ResolverValue ObjectRef) (selections : List Selection)
    : RunEnsures (Completed [])
        (executeRootSelectionSetCore schema resolvers variables fuel parentType source
          selections) := by
  simp only [executeRootSelectionSetCore]
  refine runEnsures_bind (fun _ : FieldCollection => True) _ _ _ (fun _ => trivial) ?_
  intro collection _
  exact executePlan_declarations schema resolvers variables fuel parentType source collection
    [] [] []

end GraphQL.IncrementalDelivery.ReferenceWorkQueue.DeclarationCoverage
