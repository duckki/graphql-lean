import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.WorkKeyRenaming

/-! One delivery-key map through object metadata, planning and ancestor lookup.
Injectivity preserves identity tests; labels, selections, response names and order stay
unchanged. RecursiveExecutionConstruction constructs the map from recursive cancellation. -/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.KeyRenaming

open GraphQL.IncrementalDelivery.Execution

-----------------------------------------------------------------------------------------
-- Metadata uses the same map as retained Work
-----------------------------------------------------------------------------------------

def usage (keys : Nat → Nat) (original : DeferUsage) : DeferUsage :=
  { original with ref := keys original.ref, ancestors := original.ancestors.map keys }

def field (keys : Nat → Nat) (original : FieldDetails) : FieldDetails :=
  { original with deferUsage := original.deferUsage.map (usage keys) }

def fields (keys : Nat → Nat) (original : CollectedFieldsMap) : CollectedFieldsMap :=
  original.map (fun group => (group.1, group.2.map (field keys)))

def collection (keys : Nat → Nat) (original : FieldCollection) : FieldCollection :=
  {
    collectedFieldsMap := fields keys original.collectedFieldsMap,
    newDeferUsages := original.newDeferUsages.map (usage keys)
  }

def partitions (keys : Nat → Nat) (original : List (List Nat × CollectedFieldsMap))
    : List (List Nat × CollectedFieldsMap) :=
  original.map (fun group => (group.1.map keys, fields keys group.2))

def plan (keys : Nat → Nat) (original : ExecutionPlan) : ExecutionPlan :=
  {
    collectedFieldsMap := fields keys original.collectedFieldsMap,
    newCollectedFieldsMaps := partitions keys original.newCollectedFieldsMaps
  }

-----------------------------------------------------------------------------------------
-- Identity-sensitive filtering, including duplicate and ancestor suppression
-----------------------------------------------------------------------------------------

theorem key_beq {keys : Nat → Nat} (injective : Function.Injective keys)
    (left right : Nat)
    : (keys left == keys right) = (left == right) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq]
  exact ⟨fun same => injective same, congrArg keys⟩

theorem contains_keys {keys : Nat → Nat} (injective : Function.Injective keys)
    (original : List Nat) (key : Nat)
    : (original.map keys).contains (keys key) = original.contains key := by
  induction original with
  | nil => rfl
  | cons head tail ih =>
      simp only [List.map_cons, List.contains_cons, key_beq injective, ih]

private theorem eraseDups_loop_keys {keys : Nat → Nat}
    (injective : Function.Injective keys) (original accumulated : List Nat)
    : List.eraseDupsBy.loop (· == ·) (original.map keys) (accumulated.map keys)
      = (List.eraseDupsBy.loop (· == ·) original accumulated).map keys := by
  induction original generalizing accumulated with
  | nil => simp only [List.map_nil, List.eraseDupsBy.loop, List.map_reverse]
  | cons head tail ih =>
      simp only [List.map_cons, List.eraseDupsBy.loop, List.any_map, Function.comp_def]
      have same : (fun key => keys head == keys key) = (fun key => head == key) :=
        funext (key_beq injective head)
      rw [same]
      split
      · exact ih accumulated
      · exact ih (head :: accumulated)

theorem eraseDups_keys {keys : Nat → Nat} (injective : Function.Injective keys)
    (original : List Nat)
    : (original.map keys).eraseDups = original.eraseDups.map keys := by
  exact eraseDups_loop_keys injective original []

theorem filtered_usages {keys : Nat → Nat} (injective : Function.Injective keys)
    (original : List FieldDetails)
    : getFilteredDeferUsageSet (original.map (field keys))
      = (getFilteredDeferUsageSet original).map keys := by
  have absent : (fun value => (field keys value).deferUsage.isNone)
      = (fun value => value.deferUsage.isNone) := by
    funext value
    cases known : value.deferUsage <;> simp only [field, known, Option.map_none,
      Option.map_some, Option.isNone_none, Option.isNone_some]
  have usages : (original.map (field keys)).filterMap FieldDetails.deferUsage
      = (original.filterMap FieldDetails.deferUsage).map (usage keys) := by
    simp only [List.filterMap_map, List.map_filterMap]
    rfl
  simp only [getFilteredDeferUsageSet, List.any_map, Function.comp_def, absent]
  split
  · simp_all only [List.map_nil]
  · rw [usages]
    have mapped : ((original.filterMap FieldDetails.deferUsage).map (usage keys)).map
        DeferUsage.ref = ((original.filterMap FieldDetails.deferUsage).map
          DeferUsage.ref).map keys := by
      simp only [List.map_map]
      rfl
    rw [mapped]
    rw [eraseDups_keys injective, List.filter_map]
    apply congrArg (List.map keys)
    apply congrArg (fun predicate => List.filter predicate _)
    funext key
    simp only [Function.comp_def, List.any_map, usage, key_beq injective,
      contains_keys injective]

theorem usage_sets {keys : Nat → Nat} (injective : Function.Injective keys)
    (left right : List Nat)
    : deferUsageSetsEquivalent (left.map keys) (right.map keys)
      = deferUsageSetsEquivalent left right := by
  simp only [deferUsageSetsEquivalent, List.all_map, Function.comp_def,
    contains_keys injective]

-----------------------------------------------------------------------------------------
-- Ordered collection maps and execution partitions
-----------------------------------------------------------------------------------------

theorem add_fields (keys : Nat → Nat) (group : Name × List FieldDetails)
    (original : CollectedFieldsMap)
    : CollectedFieldsMap.addFieldSet (group.1, group.2.map (field keys))
        (fields keys original)
      = fields keys (CollectedFieldsMap.addFieldSet group original) := by
  induction original with
  | nil => rfl
  | cons head tail ih =>
      simp only [fields, List.map_cons, CollectedFieldsMap.addFieldSet]
      split <;> simp_all only [List.map_append, fields, List.map_cons]

theorem merge_fields (keys : Nat → Nat) (left right : CollectedFieldsMap)
    : CollectedFieldsMap.merge (fields keys left) (fields keys right)
      = fields keys (CollectedFieldsMap.merge left right) := by
  induction right generalizing left with
  | nil => rfl
  | cons head tail ih =>
      change CollectedFieldsMap.merge
        (CollectedFieldsMap.addFieldSet (head.1, head.2.map (field keys)) (fields keys left))
        (fields keys tail) = fields keys
          (CollectedFieldsMap.merge (CollectedFieldsMap.addFieldSet head left) tail)
      rw [add_fields]
      exact ih _

theorem append_collection (keys : Nat → Nat) (left right : FieldCollection)
    : (collection keys left).append (collection keys right)
      = collection keys (left.append right) := by
  simp only [FieldCollection.append, collection, List.map_append, merge_fields]

theorem add_partition {keys : Nat → Nat} (injective : Function.Injective keys)
    (usages : List Nat) (group : Name × List FieldDetails)
    (original : List (List Nat × CollectedFieldsMap))
    : addExecutionPartition (usages.map keys) (group.1, group.2.map (field keys))
        (partitions keys original)
      = partitions keys (addExecutionPartition usages group original) := by
  induction original with
  | nil => rfl
  | cons head tail ih =>
      simp only [partitions, List.map_cons, addExecutionPartition, usage_sets injective]
      split
      · simp_all only [fields, List.map_append, List.map_cons, List.map_nil]
      · simp_all only [partitions, List.map_cons]

theorem build_plan {keys : Nat → Nat} (injective : Function.Injective keys)
    (original : CollectedFieldsMap) (parent : List Nat)
    : buildExecutionPlan (fields keys original) (parent.map keys)
      = plan keys (buildExecutionPlan original parent) := by
  suffices ∀ initial : ExecutionPlan,
      (fields keys original).foldl
        (fun current group =>
          let usages := getFilteredDeferUsageSet group.2
          if deferUsageSetsEquivalent usages (parent.map keys) then
            { current with collectedFieldsMap := current.collectedFieldsMap ++ [group] }
          else { current with newCollectedFieldsMaps :=
            addExecutionPartition usages group current.newCollectedFieldsMaps })
        (plan keys initial)
      = plan keys (original.foldl
        (fun current group =>
          let usages := getFilteredDeferUsageSet group.2
          if deferUsageSetsEquivalent usages parent then
            { current with collectedFieldsMap := current.collectedFieldsMap ++ [group] }
          else { current with newCollectedFieldsMaps :=
            addExecutionPartition usages group current.newCollectedFieldsMaps }) initial) by
    exact this {}
  intro initial
  induction original generalizing initial with
  | nil => rfl
  | cons head tail ih =>
      simp only [fields, List.map_cons, List.foldl_cons, filtered_usages injective,
        usage_sets injective]
      split <;> simp_all only
      · simpa only [plan, fields, List.map_append, List.map_cons, List.map_nil] using ih
          { initial with collectedFieldsMap := initial.collectedFieldsMap ++ [head] }
      · simpa only [plan, add_partition injective, fields] using ih
          { initial with newCollectedFieldsMaps :=
              (addExecutionPartition (getFilteredDeferUsageSet head.2) head
                initial.newCollectedFieldsMaps) }

-----------------------------------------------------------------------------------------
-- Ancestors are looked up in the same growing mapped context
-----------------------------------------------------------------------------------------

theorem lookup_fragment {keys : Nat → Nat} (injective : Function.Injective keys)
    (context : DeferMap) (key : Nat)
    : lookupDeferredFragment? (context.map (fragment keys)) (keys key)
      = (lookupDeferredFragment? context key).map (fragment keys) := by
  induction context with
  | nil => rfl
  | cons head tail ih =>
      simp only [lookupDeferredFragment?, List.map_cons, List.find?_cons, fragment, node,
        key_beq injective]
      split <;> simp_all only [Option.map_some, fragment, node,
        lookupDeferredFragment?]

theorem new_defer_map {keys : Nat → Nat} (injective : Function.Injective keys)
    (usages : List DeferUsage) (path : ResponsePath) (context : DeferMap)
    : getNewDeferMap (usages.map (usage keys)) path (context.map (fragment keys))
      = (getNewDeferMap usages path context).map (fragment keys) := by
  induction usages generalizing context with
  | nil => rfl
  | cons head tail ih =>
      simp only [getNewDeferMap, List.map_cons, List.foldl_cons]
      have ancestors : (head.ancestors.map keys).filterMap
          (fun key => (lookupDeferredFragment? (context.map (fragment keys)) key).map
            DeferredFragment.node)
        = (head.ancestors.filterMap
          (fun key => (lookupDeferredFragment? context key).map DeferredFragment.node)).map
            (node keys) := by
        simp only [List.filterMap_map, List.map_filterMap, Function.comp_def,
          lookup_fragment injective, Option.map_map, fragment]
      simp only [getNewDeferMap] at ih
      have later := ih (context ++ [{
          node := { ref := head.ref, path := path, label := head.label },
          ancestors := head.ancestors.filterMap
            (fun key => (lookupDeferredFragment? context key).map DeferredFragment.node) }])
      simp only [List.map_append, List.map_cons, List.map_nil, fragment, node] at later
      simpa only [usage, ancestors] using later

/-- Exact object metadata edge: a single injective map transports both plan partitioning
and the original public ancestor-map construction, without replacing either algorithm. -/
def ObjectMetadataRenaming : Prop :=
  ∀ keys : Nat → Nat,
    Function.Injective keys
    → (∀ original parent,
        buildExecutionPlan (fields keys original) (parent.map keys)
        = plan keys (buildExecutionPlan original parent))
      ∧ (∀ usages path context,
          getNewDeferMap (usages.map (usage keys)) path (context.map (fragment keys))
          = (getNewDeferMap usages path context).map (fragment keys))

theorem objectMetadataRenaming_holds : ObjectMetadataRenaming :=
  fun _ injective => ⟨build_plan injective, new_defer_map injective⟩

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.KeyRenaming
