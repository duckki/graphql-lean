import GraphQL.IncrementalDelivery.WorkQueueImplementation
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupRecords
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ExecutedAncestorChains
import Proofs.GraphQL.IncrementalDelivery.Correctness.Initialization
import Proofs.GraphQL.IncrementalDelivery.Correctness.DependencyKeys
import Proofs.GraphQL.IncrementalDelivery.WorkQueueSemantics.FailureReporting
import Proofs.GraphQL.IncrementalDelivery.WorkQueueSemantics.FailureExtension
import Proofs.GraphQL.IncrementalDelivery.WorkQueueSemantics.StructuralEquivalence
import Proofs.GraphQL.IncrementalDelivery.Semantics.ExecutedKeyRoles

/-! Execution-generated contributor identities and node metadata. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Generated work has no orphan tasks
-----------------------------------------------------------------------------------------

/-- Keeping the first occurrence of each numeric key yields a duplicate-free
list. The recursive call is on the tail after removing the current key.
-/
private theorem eraseDups_nodup_nat (keys : List Nat) : keys.eraseDups.Nodup := by
  cases keys with
  | nil => simp
  | cons key rest =>
      rw [List.eraseDups_cons]
      apply List.nodup_cons.mpr
      constructor
      · intro member
        have filtered := List.mem_eraseDups.mp member
        have different := (List.mem_filter.mp filtered).2
        simp at different
      · exact eraseDups_nodup_nat (rest.filter (fun other => !other == key))
termination_by keys.length
decreasing_by
  simp_wf
  exact Nat.lt_succ_of_le (List.length_filter_le _ _)

/-- Field partitioning removes duplicate defer keys before creating execution
groups. Witness: filtering preserves the `eraseDups` invariant.
-/
private theorem getFilteredDeferUsageSet_nodup (fields : List Execution.FieldDetails)
    : (Execution.getFilteredDeferUsageSet fields).Nodup := by
  unfold Execution.getFilteredDeferUsageSet
  split
  · simp
  · exact List.Sublist.nodup List.filter_sublist (eraseDups_nodup_nat _)

/-- Looking up a duplicate-free set of defer keys cannot duplicate the
resulting contributor keys, even when some lookups fail. Witness: every
successful lookup returns a fragment with exactly its requested key.
-/
private theorem filterMap_defer_keys_nodup
    (deferMap : Execution.DeferMap) (keys : List Nat) (unique : keys.Nodup)
    : ((keys.filterMap (Execution.lookupDeferredFragment? deferMap)).map
        (fun fragment => fragment.node.key)).Nodup := by
  induction keys with
  | nil => simp
  | cons key rest ih =>
      obtain ⟨absent, restUnique⟩ := List.nodup_cons.mp unique
      cases lookup : Execution.lookupDeferredFragment? deferMap key with
      | none =>
          simpa [lookup] using ih restUnique
      | some fragment =>
          simp only [List.filterMap_cons, lookup, List.map_cons]
          apply List.nodup_cons.mpr
          constructor
          · intro member
            obtain ⟨other, otherMember, sameKey⟩ := List.mem_map.mp member
            obtain ⟨otherKey, inRest, found⟩ :=
              List.mem_filterMap.mp otherMember
            have firstKey := Semantics.Ancestry.lookup_key lookup
            have secondKey := Semantics.Ancestry.lookup_key found
            have equal : key = otherKey :=
              firstKey.symm.trans (sameKey.symm.trans secondKey)
            exact absent (equal ▸ inRest)
          · exact ih restUnique

/-- Partition merging never changes an existing key list and only inserts a
new key list supplied by the caller. Witness: induction on the partition list.
-/
private theorem addExecutionPartition_keys_nodup
    (usages : List Nat) (group : Name × List Execution.FieldDetails)
    (partitions : List (List Nat × Execution.CollectedFieldsMap))
    (newUnique : usages.Nodup)
    (oldUnique : ∀ partition ∈ partitions, partition.1.Nodup)
    : ∀ partition ∈ Execution.addExecutionPartition usages group partitions,
        partition.1.Nodup := by
  induction partitions with
  | nil =>
      intro partition member
      simp only [Execution.addExecutionPartition, List.mem_singleton] at member
      subst partition
      exact newUnique
  | cons head rest ih =>
      obtain ⟨keys, fields⟩ := head
      intro partition member
      cases equivalent : Execution.deferUsageSetsEquivalent keys usages with
      | true =>
          simp only [Execution.addExecutionPartition, equivalent,
            ↓reduceIte, List.mem_cons] at member
          rcases member with equal | tail
          · subst partition
            exact oldUnique (keys, fields) (by simp)
          · exact oldUnique partition (by simp [tail])
      | false =>
          simp only [Execution.addExecutionPartition, equivalent,
            Bool.false_eq_true, ↓reduceIte, List.mem_cons] at member
          rcases member with equal | tail
          · subst partition
            exact oldUnique (keys, fields) (by simp)
          · exact ih
              (fun next inRest => oldUnique next (by simp [inRest]))
              partition tail

/-- Every deferred execution partition created by the spec plan has distinct
contributor keys. Witness: each new set is filtered/deduplicated, and the
partition insertion preserves all earlier sets.
-/
private theorem buildExecutionPlan_partition_keys_nodup
    (fields : Execution.CollectedFieldsMap) (parent : List Nat)
    : ∀ partition ∈ (Execution.buildExecutionPlan fields parent).newCollectedFieldsMaps,
        partition.1.Nodup := by
  let step (plan : Execution.ExecutionPlan)
      (group : Name × List Execution.FieldDetails) :=
    if Execution.deferUsageSetsEquivalent
        (Execution.getFilteredDeferUsageSet group.2) parent then
      { plan with collectedFieldsMap := plan.collectedFieldsMap ++ [group] }
    else
      { plan with newCollectedFieldsMaps := (Execution.addExecutionPartition
          (Execution.getFilteredDeferUsageSet group.2) group
          plan.newCollectedFieldsMaps) }
  have loop (remaining : Execution.CollectedFieldsMap)
      (plan : Execution.ExecutionPlan)
      (valid : ∀ partition ∈ plan.newCollectedFieldsMaps, partition.1.Nodup)
      : ∀ partition ∈ (remaining.foldl step plan).newCollectedFieldsMaps,
          partition.1.Nodup := by
    induction remaining generalizing plan with
    | nil => exact valid
    | cons group rest ih =>
        simp only [List.foldl_cons]
        apply ih (step plan group)
        unfold step
        split
        · exact valid
        · exact addExecutionPartition_keys_nodup _ _ _
            (getFilteredDeferUsageSet_nodup group.2) valid
  change ∀ partition ∈ (fields.foldl step {}).newCollectedFieldsMaps,
    partition.1.Nodup
  exact loop fields {} (by simp)

/-- Every task immediately lowered from this Work has distinct contributors.
Child tasks are checked when their own work is released.
-/
private def immediateContributorKeysNodup (work : Execution.Work) : Prop :=
  ∀ address task,
    task ∈ (Work.fromExecution work address).tasks
    → (task.groups.map Execution.DeliveryNode.key).Nodup

/-- Combining sibling work preserves distinct keys in each immediate task.
Witness: the lowering concatenates task lists without changing their groups.
-/
private theorem immediateContributorKeysNodup_combine
    {left right : Execution.Work}
    (leftUnique : immediateContributorKeysNodup left)
    (rightUnique : immediateContributorKeysNodup right)
    : immediateContributorKeysNodup (.combine left right) := by
  intro address task member
  simp only [Work.fromExecution, Work.combine, List.mem_append] at member
  rcases member with inLeft | inRight
  · exact leftUnique (address ++ [0]) task inLeft
  · exact rightUnique (address ++ [1]) task inRight

/-- The one execution-group task lowered at an address retains precisely the
distinct keys in its spec fragment list.
-/
private theorem immediateContributorKeysNodup_executionGroup
    {groups : List Execution.DeferredFragment} {path : Execution.ResponsePath}
    {result : Execution.Result (List (Name × Execution.ResponseValue))}
    {children : Execution.Work}
    (unique : (groups.map (fun group => group.node.key)).Nodup)
    : immediateContributorKeysNodup (.executionGroup groups path result children) := by
  intro address task member
  simp only [Work.fromExecution, List.mem_singleton] at member
  subst task
  simpa only [List.map_map, Function.comp_def] using unique

/-- `CollectExecutionGroups` lowers every partition into an immediate task
whose contributor keys are distinct. Witness: plan uniqueness, key-preserving
lookup, and induction through the stateful list recursion.
-/
private theorem collectExecutionGroups_immediateKeysNodup
    {ObjectRef : Type} (schema : Schema)
    (resolvers : Execution.Resolvers ObjectRef)
    (variables : Execution.VariableValues) (fuel : Nat)
    (parentType : Name) (source : Execution.ResolverValue ObjectRef)
    (partitions : List (List Nat × Execution.CollectedFieldsMap))
    (path : Execution.ResponsePath) (deferMap : Execution.DeferMap)
    (unique : ∀ partition ∈ partitions, partition.1.Nodup)
    (state : Nat)
    : immediateContributorKeysNodup
        ((Execution.collectExecutionGroups schema resolvers variables fuel
            parentType source partitions path deferMap).run
          state).1 := by
  induction partitions generalizing state with
  | nil =>
      intro address task member
      simp [Execution.collectExecutionGroups, StateT.run_pure, Semantics.id_pure_eq,
        Work.fromExecution] at member
  | cons partition rest ih =>
      obtain ⟨usages, fields⟩ := partition
      have headUnique : usages.Nodup := unique (usages, fields) (by simp)
      have tailUnique : ∀ partition ∈ rest, partition.1.Nodup := by
        intro next member
        exact unique next (List.mem_cons_of_mem (usages, fields) member)
      simp only [Execution.collectExecutionGroups, Execution.executeExecutionGroup,
        Semantics.run_bind, StateT.run_pure, Semantics.id_pure_eq]
      apply immediateContributorKeysNodup_combine
      · exact immediateContributorKeysNodup_executionGroup
          (filterMap_defer_keys_nodup deferMap usages headUnique)
      · exact ih tailUnique _

/-- Tasks collected from an actual execution plan inherit its duplicate-free
defer usage sets. This discharges contributor uniqueness at the plan-to-queue
boundary, without assuming anything about nested work yet.
-/
private theorem collectPlannedExecutionGroups_immediateKeysNodup
    {ObjectRef : Type} (schema : Schema)
    (resolvers : Execution.Resolvers ObjectRef)
    (variables : Execution.VariableValues) (fuel : Nat)
    (parentType : Name) (source : Execution.ResolverValue ObjectRef)
    (fields : Execution.CollectedFieldsMap) (parent : List Nat)
    (path : Execution.ResponsePath) (deferMap : Execution.DeferMap)
    (state : Nat)
    : immediateContributorKeysNodup
        ((Execution.collectExecutionGroups schema resolvers variables fuel
            parentType source
            (Execution.buildExecutionPlan fields parent).newCollectedFieldsMaps
            path deferMap).run
          state).1 :=
  collectExecutionGroups_immediateKeysNodup
    schema resolvers variables fuel parentType source _ path deferMap
    (buildExecutionPlan_partition_keys_nodup fields parent) state

/-- Every execution-group node, including those inside deferred and streamed
children, has a duplicate-free contributor list. This is proof-only metadata
of the finite spec Work, not a queue runtime field.
-/
private def contributorKeysNodup : Execution.Work → Prop
  | .empty => True
  | .combine left right => contributorKeysNodup left ∧ contributorKeysNodup right
  | .executionGroup groups _ _ children =>
      (groups.map (fun group => group.node.key)).Nodup ∧ contributorKeysNodup children
  | .stream _ items => ∀ item ∈ items, contributorKeysNodup item.2
termination_by work => sizeOf work
decreasing_by
  all_goals simp_wf
  all_goals try decreasing_trivial
  have smaller := List.sizeOf_lt_of_mem ‹item ∈ items›
  rcases item with ⟨result, work⟩
  simp only [Prod.mk.sizeOf_spec] at smaller
  dsimp only
  omega

/-- Every located subtree inherits contributor uniqueness from its root.
Witness: follow the structural location proof one child edge at a time.
-/
private theorem contributorKeysNodup_located
    {root current : Execution.Work} {address : Address}
    {producer : Option Occurrence} {owners : Keys}
    (unique : contributorKeysNodup root)
    (located : Located root address current producer owners)
    : contributorKeysNodup current := by
  have former := WorkQueueSemantics.StructuralEquivalence.located_of_current located
  induction former with
  | root => exact unique
  | left parent ih =>
      have parentUnique := ih parent.toCurrent
      simp only [contributorKeysNodup] at parentUnique
      exact parentUnique.1
  | right parent ih =>
      have parentUnique := ih parent.toCurrent
      simp only [contributorKeysNodup] at parentUnique
      exact parentUnique.2
  | executionGroup parent ih =>
      have parentUnique := ih parent.toCurrent
      simp only [contributorKeysNodup] at parentUnique
      exact parentUnique.2
  | item parent entry ih =>
      have parentUnique := ih parent.toCurrent
      simp only [contributorKeysNodup] at parentUnique
      exact parentUnique _ (List.mem_of_getElem? entry)

/-- A structural task in contributor-unique Work has a duplicate-free owner
list. Stream items have a singleton owner; execution groups inherit the
uniqueness of their own stored fragment list.
-/
private theorem contributorKeysNodup_taskOwners
    {work : Execution.Work} (unique : contributorKeysNodup work)
    {occurrence : Occurrence} {owners : Keys}
    {producer : Option Occurrence} {payload : Payload}
    (known : TaskAt work occurrence owners producer payload)
    : owners.Nodup := by
  cases occurrence with
  | executionGroup address =>
      obtain ⟨groups, path, result, children, enclosing, located,
        rfl, _⟩ := known
      have localUnique := contributorKeysNodup_located unique located
      simp only [contributorKeysNodup] at localUnique
      exact localUnique.1
  | item address index =>
      obtain ⟨node, items, enclosing, result, children, located,
        entry, rfl, _⟩ := known
      simp

/-- Sibling Work trees retain whole-tree contributor uniqueness independently.
Witness: the property follows both sides of the spec's `combine` constructor.
-/
private theorem contributorKeysNodup_combine
    {left right : Execution.Work}
    (leftUnique : contributorKeysNodup left)
    (rightUnique : contributorKeysNodup right)
    : contributorKeysNodup (.combine left right) := by
  simp only [contributorKeysNodup]
  exact ⟨leftUnique, rightUnique⟩

/-- A completion has duplicate-free contributors throughout its retained Work.
The result/error branch may discard that work but never adds task owners.
-/
private def completionContributorsNodup (completed : Execution.Completion α) : Prop :=
  contributorKeysNodup completed.work

private theorem completionContributorsNodup_pure (value : α)
    : completionContributorsNodup (Execution.Completion.pure value) := by
  simp [completionContributorsNodup, Execution.Completion.pure,
    contributorKeysNodup]

private theorem completionContributorsNodup_error (errors : Nat)
    : completionContributorsNodup (Execution.Completion.error (α := α) errors) := by
  simp [completionContributorsNodup, Execution.Completion.error,
    contributorKeysNodup]

private theorem completionContributorsNodup_map (f : α → β)
    {completed : Execution.Completion α}
    (unique : completionContributorsNodup completed)
    : completionContributorsNodup (completed.map f) := by
  cases completed with
  | mk result work =>
      cases result with
      | error errors =>
          simp [Execution.Completion.map, Execution.Completion.error,
            completionContributorsNodup, contributorKeysNodup]
      | ok result =>
          simpa [Execution.Completion.map, completionContributorsNodup] using unique

private theorem completionContributorsNodup_catchNull
    (wrap : α → Execution.ResponseValue)
    {completed : Execution.Completion α}
    (unique : completionContributorsNodup completed)
    : completionContributorsNodup (completed.catchNull wrap) := by
  cases completed with
  | mk result work =>
      cases result with
      | error errors =>
          simp [Execution.Completion.catchNull, completionContributorsNodup,
            contributorKeysNodup]
      | ok result =>
          simpa [Execution.Completion.catchNull, completionContributorsNodup] using unique

private theorem completionContributorsNodup_nonNull
    {completed : Execution.Completion Execution.ResponseValue}
    (unique : completionContributorsNodup completed)
    : completionContributorsNodup completed.nonNull := by
  unfold Execution.Completion.nonNull
  split
  · exact completionContributorsNodup_error _
  · exact unique

private theorem completionContributorsNodup_combine (f : α → β → γ)
    {left : Execution.Completion α} {right : Execution.Completion β}
    (leftUnique : completionContributorsNodup left)
    (rightUnique : completionContributorsNodup right)
    : completionContributorsNodup (Execution.Completion.combine f left right) := by
  cases result : Execution.Result.combine f left.result right.result with
  | error errors =>
      simp [Execution.Completion.combine, result,
        completionContributorsNodup_error]
  | ok value =>
      simpa [Execution.Completion.combine, result, completionContributorsNodup]
        using contributorKeysNodup_combine leftUnique rightUnique

/-- `CollectExecutionGroups` preserves whole-tree contributor uniqueness if
each completed partition's child Work does. The remaining child premise is a
property of resolver execution, not an assumption on host settlement order.
-/
private theorem collectExecutionGroups_contributorKeysNodup
    {ObjectRef : Type} (schema : Schema)
    (resolvers : Execution.Resolvers ObjectRef)
    (variables : Execution.VariableValues) (fuel : Nat)
    (parentType : Name) (source : Execution.ResolverValue ObjectRef)
    (partitions : List (List Nat × Execution.CollectedFieldsMap))
    (path : Execution.ResponsePath) (deferMap : Execution.DeferMap)
    (unique : ∀ partition ∈ partitions, partition.1.Nodup)
    (childUnique
      : ∀ partition ∈ partitions,
          ∀ state,
            contributorKeysNodup
              ((Execution.executeExecutionGroup schema resolvers variables fuel
                  parentType source partition.2 path partition.1 deferMap).run
                state).1.work)
    (state : Nat)
    : contributorKeysNodup
        ((Execution.collectExecutionGroups schema resolvers variables fuel
            parentType source partitions path deferMap).run
          state).1 := by
  induction partitions generalizing state with
  | nil =>
      simp [Execution.collectExecutionGroups, StateT.run_pure,
        Semantics.id_pure_eq, contributorKeysNodup]
  | cons partition rest ih =>
      obtain ⟨usages, fields⟩ := partition
      have headUnique : usages.Nodup := unique (usages, fields) (by simp)
      have tailUnique : ∀ partition ∈ rest, partition.1.Nodup := by
        intro next member
        exact unique next (List.mem_cons_of_mem (usages, fields) member)
      have headWorkUnique (middle : Nat) : contributorKeysNodup
          ((Execution.executeExecutionGroup schema resolvers variables fuel
            parentType source fields path usages deferMap).run middle).1.work :=
        childUnique (usages, fields) (by simp) middle
      have tailWorkUnique : ∀ partition ∈ rest, ∀ middle,
          contributorKeysNodup
            ((Execution.executeExecutionGroup schema resolvers variables fuel
              parentType source partition.2 path partition.1 deferMap).run middle).1.work := by
        intro next member middle
        exact childUnique next (List.mem_cons_of_mem (usages, fields) member) middle
      simp only [Execution.collectExecutionGroups, Semantics.run_bind,
        StateT.run_pure, Semantics.id_pure_eq]
      apply contributorKeysNodup_combine
      · simp only [contributorKeysNodup]
        exact ⟨filterMap_defer_keys_nodup deferMap usages headUnique,
          headWorkUnique state⟩
      · exact ih tailUnique tailWorkUnique _

/-- The field collector preserves whole-tree contributor uniqueness provided
each field's proof-only execution boundary does. The list recursion adds no
new owners; it only combines the two retained Work trees.
-/
private theorem executeCollectedFields_contributorKeysNodup_of_fields
    {ObjectRef : Type} (schema : Schema)
    (resolvers : Execution.Resolvers ObjectRef)
    (variables : Execution.VariableValues) (fuel : Nat)
    (parentType : Name) (source : Execution.ResolverValue ObjectRef)
    (fields : Execution.CollectedFieldsMap)
    (path : Execution.ResponsePath) (usages : List Nat)
    (deferMap : Execution.DeferMap)
    (fieldUnique
      : ∀ group ∈ fields,
          Semantics.RunEnsures completionContributorsNodup
            (Semantics.executeResponseField schema resolvers variables fuel
              parentType source group.1 group.2 path usages deferMap))
    : Semantics.RunEnsures completionContributorsNodup
        (Execution.executeCollectedFields schema resolvers variables fuel
          parentType source fields path usages deferMap) := by
  induction fields with
  | nil =>
      rw [Semantics.executeCollectedFields_nil]
      exact Semantics.runEnsures_pure _ _ (completionContributorsNodup_pure [])
  | cons group rest ih =>
      obtain ⟨responseName, selected⟩ := group
      rw [Semantics.executeCollectedFields_cons]
      refine Semantics.runEnsures_bind completionContributorsNodup
        completionContributorsNodup _ _ ?_ ?_
      · exact fieldUnique (responseName, selected) (by simp)
      · intro head headUnique
        refine Semantics.runEnsures_bind completionContributorsNodup
          completionContributorsNodup _ _ ?_ ?_
        · apply ih
          intro next member
          exact fieldUnique next (List.mem_cons_of_mem _ member)
        · intro tail tailUnique
          exact Semantics.runEnsures_pure _ _
            (completionContributorsNodup_combine List.append
              headUnique tailUnique)

/-- Response-field execution either returns no Work or preserves the Work of
`CompleteValue`. The latter is the sole recursive premise needed here.
-/
private theorem executeResponseField_contributorKeysNodup_of_value
    {ObjectRef : Type} (schema : Schema)
    (resolvers : Execution.Resolvers ObjectRef)
    (variables : Execution.VariableValues) (fuel : Nat)
    (parentType : Name) (source : Execution.ResolverValue ObjectRef)
    (responseName : Name) (selected : List Execution.FieldDetails)
    (path : Execution.ResponsePath) (usages : List Nat)
    (deferMap : Execution.DeferMap)
    (valueUnique
      : ∀ (innerFuel : Nat) (definition : FieldDefinition) resolved,
          fuel = innerFuel + 1
          → Semantics.RunEnsures completionContributorsNodup
              (Execution.completeValue schema resolvers variables innerFuel
                definition.outputType selected resolved (path ++ [.field responseName])
                usages deferMap true))
    : Semantics.RunEnsures completionContributorsNodup
        (Semantics.executeResponseField schema resolvers variables fuel
          parentType source responseName selected path usages deferMap) := by
  cases fuel with
  | zero =>
      simp only [Semantics.executeResponseField]
      exact Semantics.runEnsures_pure _ _ (completionContributorsNodup_error _)
  | succ innerFuel =>
      cases selected with
      | nil =>
          simp only [Semantics.executeResponseField]
          exact Semantics.runEnsures_pure _ _ (completionContributorsNodup_error _)
      | cons field rest =>
          simp only [Semantics.executeResponseField]
          split
          · exact Semantics.runEnsures_pure _ _
              (completionContributorsNodup_error _)
          · split
            · exact Semantics.runEnsures_pure _ _
                (by simp [completionContributorsNodup, contributorKeysNodup])
            · split
              · exact Semantics.runEnsures_pure _ _
                  (by simp [completionContributorsNodup, contributorKeysNodup])
              · refine Semantics.runEnsures_bind completionContributorsNodup
                  completionContributorsNodup _ _ ?_ ?_
                · exact valueUnique innerFuel _ _ rfl
                · intro completed unique
                  exact Semantics.runEnsures_pure _ _
                    (completionContributorsNodup_map _ unique)

/-- Ordinary list completion combines the Work of its items, preserving
contributor uniqueness whenever each item completion preserves it.
-/
private theorem completeListValue_contributorKeysNodup_of_values
    {ObjectRef : Type} (schema : Schema)
    (resolvers : Execution.Resolvers ObjectRef)
    (variables : Execution.VariableValues) (fuel : Nat)
    (itemType : TypeRef) (selected : List Execution.FieldDetails)
    (path : Execution.ResponsePath) (usages : List Nat)
    (deferMap : Execution.DeferMap)
    (valueUnique
      : ∀ index value,
          Semantics.RunEnsures completionContributorsNodup
            (Execution.completeValue schema resolvers variables fuel itemType
              selected value (path ++ [.index index]) usages deferMap false))
    (values : List (Execution.ResolverValue ObjectRef)) (index : Nat)
    : Semantics.RunEnsures completionContributorsNodup
        (Execution.completeListValue schema resolvers variables fuel itemType
          selected values path index usages deferMap) := by
  induction values generalizing index with
  | nil =>
      simp only [Execution.completeListValue]
      exact Semantics.runEnsures_pure _ _ (completionContributorsNodup_pure [])
  | cons value rest ih =>
      simp only [Execution.completeListValue]
      refine Semantics.runEnsures_bind completionContributorsNodup
        completionContributorsNodup _ _ ?_ ?_
      · exact valueUnique index value
      · intro head headUnique
        refine Semantics.runEnsures_bind completionContributorsNodup
          completionContributorsNodup _ _ ?_ ?_
        · exact ih (index + 1)
        · intro tail tailUnique
          exact Semantics.runEnsures_pure _ _
            (completionContributorsNodup_combine List.cons
              headUnique tailUnique)

/-- Stream item completion stores only each successful item's Work; an item
failure stores empty Work. The recursive tail preserves the same invariant.
-/
private def streamItemsContributorsNodup
    (items : List (Execution.Result Execution.ResponseValue × Execution.Work))
    : Prop :=
  ∀ item ∈ items, contributorKeysNodup item.2

private theorem completeStreamItems_contributorKeysNodup_of_values
    {ObjectRef : Type} (schema : Schema)
    (resolvers : Execution.Resolvers ObjectRef)
    (variables : Execution.VariableValues) (fuel : Nat)
    (itemType : TypeRef) (selected : List Execution.FieldDetails)
    (path : Execution.ResponsePath)
    (valueUnique
      : ∀ index value,
          Semantics.RunEnsures completionContributorsNodup
            (Execution.completeValue schema resolvers variables fuel itemType
              selected value (path ++ [.index index]) [] [] false))
    (values : List (Execution.ResolverValue ObjectRef)) (index : Nat)
    : Semantics.RunEnsures streamItemsContributorsNodup
        (Execution.completeStreamItems schema resolvers variables fuel itemType
          selected values path index) := by
  induction values generalizing index with
  | nil =>
      simp only [Execution.completeStreamItems]
      exact Semantics.runEnsures_pure _ _ (by simp [streamItemsContributorsNodup])
  | cons value rest ih =>
      simp only [Execution.completeStreamItems]
      refine Semantics.runEnsures_bind completionContributorsNodup
        streamItemsContributorsNodup _ _ ?_ ?_
      · exact valueUnique index value
      · intro head headUnique
        cases result : head.result with
        | error errors =>
            exact Semantics.runEnsures_pure _ _
              (by simp [streamItemsContributorsNodup, contributorKeysNodup])
        | ok data =>
            refine Semantics.runEnsures_bind streamItemsContributorsNodup
              streamItemsContributorsNodup _ _ ?_ ?_
            · exact ih (index + 1)
            · intro tail tailUnique
              exact Semantics.runEnsures_pure _ _
                (by
                  change ∀ item ∈ (Except.ok data, head.work) :: tail,
                    contributorKeysNodup item.2
                  intro item member
                  rcases List.mem_cons.mp member with same | inTail
                  · subst item
                    exact headUnique
                  · exact tailUnique item inTail)

/-- The stream hook combines a completed initial list with a stream whose
remaining item children each preserve contributor uniqueness. If the stream
boundary is never reached, it returns the ordinary list completion unchanged.
-/
private theorem completeListValueWithStream_contributorKeysNodup_of_values
    {ObjectRef : Type} (schema : Schema)
    (resolvers : Execution.Resolvers ObjectRef)
    (variables : Execution.VariableValues) (fuel : Nat)
    (itemType : TypeRef) (selected : List Execution.FieldDetails)
    (values : List (Execution.ResolverValue ObjectRef))
    (path : Execution.ResponsePath) (usages : List Nat)
    (deferMap : Execution.DeferMap) (allowStream : Bool)
    (valueUnique
      : ∀ index value,
          Semantics.RunEnsures completionContributorsNodup
            (Execution.completeValue schema resolvers variables fuel itemType
              selected value (path ++ [.index index]) usages deferMap false))
    (streamValueUnique
      : ∀ index value,
          Semantics.RunEnsures completionContributorsNodup
            (Execution.completeValue schema resolvers variables fuel itemType
              (selected.map (fun field => { field with deferUsage := none }))
              value (path ++ [.index index]) [] [] false))
    : Semantics.RunEnsures completionContributorsNodup
        (Execution.completeListValueWithStream schema resolvers variables fuel
          itemType selected values path usages deferMap allowStream) := by
  unfold Execution.completeListValueWithStream
  dsimp only
  split
  · exact Semantics.runEnsures_pure _ _
      (by simp [completionContributorsNodup, contributorKeysNodup])
  · refine Semantics.runEnsures_bind completionContributorsNodup
      completionContributorsNodup _ _ ?_ ?_
    · exact completeListValue_contributorKeysNodup_of_values
        schema resolvers variables fuel itemType selected path usages deferMap
        valueUnique values 0
    · intro initial initialUnique
      exact Semantics.runEnsures_pure _ _
        (completionContributorsNodup_catchNull Execution.ResponseValue.list
          initialUnique)
  · rename_i usage _
    refine Semantics.runEnsures_bind completionContributorsNodup
      completionContributorsNodup _ _ ?_ ?_
    · exact completeListValue_contributorKeysNodup_of_values
        schema resolvers variables fuel itemType selected path usages deferMap
        valueUnique (values.take usage.initialCount) 0
    · intro initial initialUnique
      rcases initial with ⟨initialResult, initialWork⟩
      cases initialResult with
      | error errors =>
          exact Semantics.runEnsures_pure _ _
            (completionContributorsNodup_catchNull Execution.ResponseValue.list
              initialUnique)
      | ok result =>
          by_cases short : values.length < usage.initialCount
          · simp only [short, ↓reduceIte]
            exact Semantics.runEnsures_pure _ _
              (completionContributorsNodup_catchNull Execution.ResponseValue.list
                initialUnique)
          · simp only [short, ↓reduceIte]
            refine Semantics.runEnsures_bind (fun _ : Nat => True)
              completionContributorsNodup _ _ (fun _ => trivial) ?_
            intro key _
            refine Semantics.runEnsures_bind streamItemsContributorsNodup
              completionContributorsNodup _ _ ?_ ?_
            · exact completeStreamItems_contributorKeysNodup_of_values
                schema resolvers variables fuel itemType _ path
                streamValueUnique (values.drop usage.initialCount)
                usage.initialCount
            · intro items itemsUnique
              apply Semantics.runEnsures_pure
              have initialWorkUnique :=
                completionContributorsNodup_catchNull Execution.ResponseValue.list
                  initialUnique
              have streamUnique : contributorKeysNodup
                  (.stream { key := key, path := path, label := usage.label } items) := by
                change ∀ item ∈ items, contributorKeysNodup item.2 at itemsUnique
                simpa only [contributorKeysNodup] using itemsUnique
              exact contributorKeysNodup_combine initialWorkUnique streamUnique

/-- All value completions at one fuel preserve contributor uniqueness, for
every resolver type and execution context. This packages the outer induction
over fuel; non-null recursion is handled by the smaller type wrapper.
-/
private def valuePreservesContributors (fuel : Nat) : Prop :=
  ∀ (ObjectRef : Type) (schema : Schema)
    (resolvers : Execution.Resolvers ObjectRef)
    (variables : Execution.VariableValues) (fieldType : TypeRef)
    (selected : List Execution.FieldDetails)
    (value : Execution.ResolverValue ObjectRef)
    (path : Execution.ResponsePath) (usages : List Nat)
    (deferMap : Execution.DeferMap) (allowStream : Bool),
    Semantics.RunEnsures completionContributorsNodup
      (Execution.completeValue schema resolvers variables fuel fieldType
        selected value path usages deferMap allowStream)

/-- A field execution at fuel `n` only calls value completion at smaller fuel.
Witness: the resolver branch consumes one fuel layer before `CompleteValue`.
-/
private theorem executeResponseField_contributors_of_prior
    {ObjectRef : Type} (schema : Schema)
    (resolvers : Execution.Resolvers ObjectRef)
    (variables : Execution.VariableValues) (fuel : Nat)
    (parentType : Name) (source : Execution.ResolverValue ObjectRef)
    (responseName : Name) (selected : List Execution.FieldDetails)
    (path : Execution.ResponsePath) (usages : List Nat)
    (deferMap : Execution.DeferMap)
    (prior : ∀ smaller < fuel, valuePreservesContributors smaller)
    : Semantics.RunEnsures completionContributorsNodup
        (Semantics.executeResponseField schema resolvers variables fuel
          parentType source responseName selected path usages deferMap) := by
  apply executeResponseField_contributorKeysNodup_of_value
  intro innerFuel definition resolved equal
  exact prior innerFuel (by omega) ObjectRef schema resolvers variables
    definition.outputType selected resolved (path ++ [.field responseName])
    usages deferMap true

/-- Field collection at fuel `n` combines only fields whose value completions
run at smaller fuel. No extra scheduler premise is needed.
-/
private theorem executeCollectedFields_contributors_of_prior
    {ObjectRef : Type} (schema : Schema)
    (resolvers : Execution.Resolvers ObjectRef)
    (variables : Execution.VariableValues) (fuel : Nat)
    (parentType : Name) (source : Execution.ResolverValue ObjectRef)
    (fields : Execution.CollectedFieldsMap)
    (path : Execution.ResponsePath) (usages : List Nat)
    (deferMap : Execution.DeferMap)
    (prior : ∀ smaller < fuel, valuePreservesContributors smaller)
    : Semantics.RunEnsures completionContributorsNodup
        (Execution.executeCollectedFields schema resolvers variables fuel
          parentType source fields path usages deferMap) := by
  apply executeCollectedFields_contributorKeysNodup_of_fields
  intro group member
  exact executeResponseField_contributors_of_prior
    schema resolvers variables fuel parentType source group.1 group.2
    path usages deferMap prior

/-- Executing a spec-built plan at fuel `n` preserves duplicate-free
contributors when all smaller-fuel completions do. The collector supplies the
same fact for its immediate and deferred partitions.
-/
private theorem executePlan_contributors_of_prior
    {ObjectRef : Type} (schema : Schema)
    (resolvers : Execution.Resolvers ObjectRef)
    (variables : Execution.VariableValues) (fuel : Nat)
    (parentType : Name) (source : Execution.ResolverValue ObjectRef)
    (newDeferUsages : List Execution.DeferUsage)
    (fields : Execution.CollectedFieldsMap)
    (path : Execution.ResponsePath) (usages : List Nat)
    (deferMap : Execution.DeferMap)
    (prior : ∀ smaller < fuel, valuePreservesContributors smaller)
    : Semantics.RunEnsures completionContributorsNodup
        (Execution.executeExecutionPlan schema resolvers variables fuel
          parentType source newDeferUsages
          (Execution.buildExecutionPlan fields usages)
          path usages deferMap) := by
  let plan := Execution.buildExecutionPlan fields usages
  let nextMap := Execution.getNewDeferMap newDeferUsages path deferMap
  simp only [Execution.executeExecutionPlan]
  refine Semantics.runEnsures_bind completionContributorsNodup
    completionContributorsNodup _ _ ?_ ?_
  · exact executeCollectedFields_contributors_of_prior
      schema resolvers variables fuel parentType source
      plan.collectedFieldsMap path usages nextMap prior
  · intro initial initialUnique
    cases initial.result with
    | error errors =>
        exact Semantics.runEnsures_pure _ _ initialUnique
    | ok result =>
        refine Semantics.runEnsures_bind contributorKeysNodup
          completionContributorsNodup _ _ ?_ ?_
        · intro state
          apply collectExecutionGroups_contributorKeysNodup
            schema resolvers variables fuel parentType source
            plan.newCollectedFieldsMaps path nextMap
          · exact buildExecutionPlan_partition_keys_nodup fields usages
          · intro partition member middle
            simpa only [Execution.executeExecutionGroup, completionContributorsNodup]
              using executeCollectedFields_contributors_of_prior
                schema resolvers variables fuel parentType source
                partition.2 path partition.1 nextMap prior middle
        · intro tasks tasksUnique
          apply Semantics.runEnsures_pure
          exact contributorKeysNodup_combine initialUnique tasksUnique

/-- Every finite pure value completion produces Work with duplicate-free
contributor lists. Witness: strong induction on fuel, with a smaller-type
descent for non-null wrappers at unchanged fuel.
-/
private theorem valuePreservesContributors_all (fuel : Nat)
    : valuePreservesContributors fuel := by
  induction fuel using Nat.strongRecOn with
  | ind fuel prior =>
      intro ObjectRef schema resolvers variables fieldType selected value path
        usages deferMap allowStream
      cases fuel with
      | zero =>
          simp only [Execution.completeValue]
          exact Semantics.runEnsures_pure _ _ (completionContributorsNodup_error _)
      | succ innerFuel =>
          induction fieldType generalizing selected value path usages deferMap
              allowStream with
          | nonNull inner innerIH =>
              simp only [Execution.completeValue]
              refine Semantics.runEnsures_bind completionContributorsNodup
                completionContributorsNodup _ _ ?_ ?_
              · exact innerIH selected value path usages deferMap allowStream
              · intro completed unique
                exact Semantics.runEnsures_pure _ _
                  (completionContributorsNodup_nonNull unique)
          | named typeName =>
              cases value with
              | null =>
                  simp only [Execution.completeValue]
                  exact Semantics.runEnsures_pure _ _
                    (completionContributorsNodup_pure Execution.ResponseValue.null)
              | scalar scalar =>
                  simp only [Execution.completeValue]
                  split
                  · exact Semantics.runEnsures_pure _ _
                      (completionContributorsNodup_error _)
                  · exact Semantics.runEnsures_pure _ _
                      (completionContributorsNodup_pure
                        (Execution.ResponseValue.scalar scalar))
              | list values =>
                  simp only [Execution.completeValue]
                  exact Semantics.runEnsures_pure _ _
                    (completionContributorsNodup_error _)
              | object runtimeType ref =>
                  simp only [Execution.completeValue]
                  split
                  · exact Semantics.runEnsures_pure _ _
                      (completionContributorsNodup_error _)
                  · refine Semantics.runEnsures_bind (fun _ : Execution.FieldCollection => True)
                      completionContributorsNodup _ _ (fun _ => trivial) ?_
                    intro collection _
                    refine Semantics.runEnsures_bind completionContributorsNodup
                      completionContributorsNodup _ _ ?_ ?_
                    · exact executePlan_contributors_of_prior schema resolvers
                        variables innerFuel runtimeType (.object runtimeType ref)
                        collection.newDeferUsages collection.collectedFieldsMap path usages deferMap
                        (fun smaller less => prior smaller (by omega))
                    · intro completed unique
                      exact Semantics.runEnsures_pure _ _
                        (completionContributorsNodup_catchNull
                          Execution.ResponseValue.object unique)
          | list inner innerIH =>
              cases value with
              | null =>
                  simp only [Execution.completeValue]
                  exact Semantics.runEnsures_pure _ _
                    (completionContributorsNodup_pure Execution.ResponseValue.null)
              | scalar scalar =>
                  simp only [Execution.completeValue]
                  exact Semantics.runEnsures_pure _ _
                    (completionContributorsNodup_error _)
              | object runtimeType ref =>
                  simp only [Execution.completeValue]
                  exact Semantics.runEnsures_pure _ _
                    (completionContributorsNodup_error _)
              | list values =>
                  simpa only [Execution.completeValue]
                    using completeListValueWithStream_contributorKeysNodup_of_values
                      schema resolvers variables innerFuel inner selected values
                      path usages deferMap allowStream
                      (fun index item =>
                        prior innerFuel (by omega) ObjectRef schema resolvers variables
                          inner selected item (path ++ [.index index]) usages deferMap
                          false)
                      (fun index item =>
                        prior innerFuel (by omega) ObjectRef schema resolvers variables
                          inner
                          (selected.map (fun field => { field with deferUsage := none }))
                          item (path ++ [.index index]) [] [] false)

/-- Root execution constructs only Work whose execution-group contributor
lists are duplicate-free. Witness: root collection followed by the checked
spec plan and the unconditional finite-fuel value-completion induction.
-/
private theorem executeRoot_contributorKeysNodup
    {ObjectRef : Type} (schema : Schema)
    (resolvers : Execution.Resolvers ObjectRef)
    (variables : Execution.VariableValues) (fuel : Nat)
    (parentType : Name) (source : Execution.ResolverValue ObjectRef)
    (selections : List Selection) (state : Nat)
    : contributorKeysNodup
        ((Execution.executeRootSelectionSetCore schema resolvers variables fuel
            parentType source selections).run
          state).1.work := by
  unfold Execution.executeRootSelectionSetCore
  apply Semantics.runEnsures_bind (fun _ : Execution.FieldCollection => True)
    completionContributorsNodup
  · intro _
    trivial
  · intro collection _
    exact executePlan_contributors_of_prior schema resolvers variables fuel
      parentType source collection.newDeferUsages collection.collectedFieldsMap [] [] []
      (fun smaller _ => valuePreservesContributors_all smaller)

/-- Generated Work has duplicate-free contributor keys at every nested
execution-group task, including groups produced under stream items.
-/
private theorem ExecutedWork.contributorKeysNodup
    {work : Execution.Work} (generated : ExecutedWork work)
    : contributorKeysNodup work := by
  obtain ⟨ObjectRef, schema, resolvers, variables, fuel, parentType, source,
    selections, equal⟩ := generated
  rw [← equal]
  exact executeRoot_contributorKeysNodup schema resolvers variables fuel
    parentType source selections 0

/-- Every execution-generated task has distinct contributing owner keys.
Witness: whole-tree uniqueness plus the structural task's located fragment
list (or the singleton owner of a stream item).
-/
theorem ExecutedWork.taskOwners_nodup
    {work : Execution.Work} (generated : ExecutedWork work)
    {occurrence : Occurrence} {owners : Keys}
    {producer : Option Occurrence} {payload : Payload}
    (known : TaskAt work occurrence owners producer payload)
    : owners.Nodup :=
  contributorKeysNodup_taskOwners generated.contributorKeysNodup known

/-- Every generated task has an owner. Witness: root execution's coherent key metadata
and the structural owner-nonemptiness theorem.
-/
theorem ExecutedWork.taskOwners_nonempty {work : Execution.Work}
    (generated : ExecutedWork work)
    {occurrence owners producer payload}
    (known : TaskAt work occurrence owners producer payload)
    : owners ≠ [] := by
  obtain ⟨ObjectRef, schema, resolvers, variables, fuel, parentType, source,
    selections, equal⟩ := generated
  obtain ⟨_, parents, _, coherent, _⟩ :=
    Semantics.GeneralScheduling.executeRoot_continuity schema resolvers variables fuel
      parentType source selections 0
  rw [← equal] at known
  exact Correctness.coherent_task_owners_nonempty coherent known

/-- A structural subwork inherits the defer/stream role assignment of the
execution-generated root. This traverses only Work's existing child edges. -/
theorem generatedWorkRoles_located
    {work current : Execution.Work} {address : Address}
    {producer : Option Occurrence} {owners : Keys}
    {roles : Semantics.KeyRoles.Assignment}
    (rootRoles : Semantics.KeyRoles.WorkRoles roles work)
    (located : StructuralEquivalence.Located work address current producer owners)
    : Semantics.KeyRoles.WorkRoles roles current := by
  induction located with
  | root => exact rootRoles
  | left _ ih =>
      simp only [Semantics.KeyRoles.WorkRoles] at ih
      exact ih.1
  | right _ ih =>
      simp only [Semantics.KeyRoles.WorkRoles] at ih
      exact ih.2
  | executionGroup _ ih =>
      simp only [Semantics.KeyRoles.WorkRoles] at ih
      exact ih.2
  | item _ entry ih =>
      simp only [Semantics.KeyRoles.WorkRoles] at ih
      exact ih.2 _ (List.mem_of_getElem? entry)

/-- Generated defer nodes have role `false`, and generated stream nodes have
role `true`, even when Work contains repeated descriptors for a shared key. -/
private theorem ExecutedWork.nodeRoles {work : Execution.Work}
    (generated : ExecutedWork work)
    : ∃ roles : Semantics.KeyRoles.Assignment,
        ∀ node kind dependencies producer,
          NodeAt work node kind dependencies producer
          → roles node.key = (kind == .stream) := by
  obtain ⟨ObjectRef, schema, resolvers, variables, fuel, parentType, source,
    selections, equal⟩ := generated
  obtain ⟨roles, rootRoles⟩ :=
    Semantics.KeyRoles.executeRoot_roles schema resolvers variables fuel
      parentType source selections 0
  rw [equal] at rootRoles
  refine ⟨roles, ?_⟩
  intro node kind dependencies producer known
  cases StructuralEquivalence.nodeAt_of_current known with
  | group located member =>
      have current := generatedWorkRoles_located rootRoles located
      simp only [Semantics.KeyRoles.WorkRoles] at current
      exact (current.1 _ member).1
  | stream located =>
      have current := generatedWorkRoles_located rootRoles located
      simp only [Semantics.KeyRoles.WorkRoles] at current
      exact current.1

/-- A generated delivery key cannot simultaneously denote a defer group and a stream.
Witness: execution assigns incompatible Boolean roles to the two node kinds. This also
rules out same-key group closures when proving openness of a referenced stream.
-/
theorem ExecutedWork.groupStreamKeysDisjoint
    {work : Execution.Work} (generated : ExecutedWork work)
    {group stream : Execution.DeliveryNode}
    {groupDependencies streamDependencies : Keys}
    {groupProducer streamProducer : Option Occurrence}
    (groupKnown : NodeAt work group .group groupDependencies groupProducer)
    (streamKnown : NodeAt work stream .stream streamDependencies streamProducer)
    : group.key ≠ stream.key := by
  obtain ⟨roles, role⟩ := generated.nodeRoles
  intro same
  have groupRole := role group .group groupDependencies groupProducer groupKnown
  have streamRole := role stream .stream streamDependencies streamProducer streamKnown
  change roles group.key = false at groupRole
  change roles stream.key = true at streamRole
  rw [same] at groupRole
  exact Bool.false_ne_true (groupRole.symm.trans streamRole)

/-- A generated work tree has one global ancestor assignment for every defer
group, including repeated occurrences of the same key in shared work. -/
private theorem ExecutedWork.groupDependenciesValid
    {work : Execution.Work} (generated : ExecutedWork work)
    : ∃ (parents : Nat → Keys) (bound : Nat),
        Semantics.Ancestry.Valid parents bound
        ∧ ∀ node dependencies producer,
            NodeAt work node .group dependencies producer
            → node.key < bound ∧ dependencies = parents node.key := by
  have locatedWorkAt {parents : Nat → Keys} {bound : Nat}
      {root current : Execution.Work} {address : Address} {producer : Option Occurrence}
      {owners : Keys}
      (rootAt : Semantics.MixedKeys.WorkAt parents 0 bound root)
      (located : StructuralEquivalence.Located root address current producer owners)
      : ∃ lower, Semantics.MixedKeys.WorkAt parents lower bound current := by
    induction located with
    | root => exact ⟨0, rootAt⟩
    | left prior ih =>
        obtain ⟨lower, currentAt⟩ := ih
        simp only [Semantics.MixedKeys.WorkAt] at currentAt
        exact ⟨lower, currentAt.1⟩
    | right prior ih =>
        obtain ⟨lower, currentAt⟩ := ih
        simp only [Semantics.MixedKeys.WorkAt] at currentAt
        exact ⟨lower, currentAt.2⟩
    | executionGroup prior ih =>
        obtain ⟨lower, currentAt⟩ := ih
        simp only [Semantics.MixedKeys.WorkAt] at currentAt
        exact ⟨lower, currentAt.2.2⟩
    | item prior entry ih =>
        obtain ⟨lower, currentAt⟩ := ih
        simp only [Semantics.MixedKeys.WorkAt] at currentAt
        exact ⟨_, currentAt.2.2 _ (List.mem_of_getElem? entry)⟩
  obtain ⟨ObjectRef, schema, resolvers, variables, fuel, parentType, source,
    selections, equal⟩ := generated
  obtain ⟨_, parents, valid, rootAt, _⟩ :=
    Semantics.GeneralScheduling.executeRoot_continuity schema resolvers
      variables fuel parentType source selections 0
  refine ⟨parents, _, valid, ?_⟩
  intro node dependencies producer known
  rw [← equal] at known
  obtain ⟨address, groups, path, result, children, enclosing, group,
    located, member, nodeEqual, dependenciesEqual⟩ := known
  obtain ⟨lower, groupAt⟩ :=
    locatedWorkAt rootAt (StructuralEquivalence.located_of_current located)
  simp only [Semantics.MixedKeys.WorkAt] at groupAt
  have fragmentAt := (groupAt.2.1 group member).2
  rw [dependenciesEqual, nodeEqual]
  exact ⟨fragmentAt.1, fragmentAt.2⟩

/-- The generated work's defer groups share one global ancestor assignment. -/
theorem ExecutedWork.groupDependenciesCanonical
    {work : Execution.Work} (generated : ExecutedWork work)
    : ∃ parents : Nat → Keys,
        ∀ node dependencies producer,
          NodeAt work node .group dependencies producer
          → dependencies = parents node.key := by
  obtain ⟨parents, _, _, canonical⟩ := generated.groupDependenciesValid
  exact ⟨parents, fun node dependencies producer known =>
    (canonical node dependencies producer known).2⟩

/-- A generated defer group with a root descriptor can fail directly through
a contributing task or through one of its defer ancestors. A root producer
excludes producer cancellation, and generated key roles exclude stream rules.
-/
theorem ExecutedWork.groupFailure_withRootProducer
    {work : Execution.Work} (generated : ExecutedWork work)
    {node : Execution.DeliveryNode} {dependencies : Keys}
    (root : NodeAt work node .group dependencies none)
    {matching events failures}
    (failure : NodeFailed work matching events failures node.key)
    : (∃ occurrence owners,
        TaskHasOwners work occurrence owners
        ∧ node.key ∈ owners
        ∧ occurrence ∈ failedBefore failures events.length)
      ∨ ∃ dependency ∈ dependencies,
          NodeFailed work matching events failures dependency := by
  obtain ⟨cut, cutMember, reached, cause⟩ := failure
  cases cause with
  | task known owner member =>
      exact .inl ⟨_, _, known, owner, failedBefore_subset failures reached member⟩
  | @groupDependency key otherDependencies dependency known member prior =>
      obtain ⟨other, producer, otherKnown, keyEq⟩ := known
      obtain ⟨parents, canonical⟩ := generated.groupDependenciesCanonical
      have rootDeps := canonical node dependencies none root
      have otherDeps := canonical other otherDependencies producer otherKnown
      have sameDeps : otherDependencies = dependencies := by
        rw [keyEq] at otherDeps
        exact otherDeps.trans rootDeps.symm
      exact .inr ⟨dependency, sameDeps ▸ member,
        cut, cutMember, reached, prior⟩
  | @streamDependencies key dependencies known _ _ =>
      obtain ⟨stream, producer, streamKnown, keyEq⟩ := known
      have separate := generated.groupStreamKeysDisjoint root streamKnown
      exact False.elim (separate (by simpa using keyEq.symm))
  | producers _ noRoot _ _ =>
      exact False.elim (noRoot ⟨node, .group, dependencies, root, rfl⟩)

/-- A generated group whose producer already published cannot fail by retroactively
cancelling that producer. Witness: move historical failure to the admitted current
snapshot, then exclude the producer-cancellation rule using the observed publication.
Only contributing-task failures and defer-ancestor failures remain possible.
-/
theorem ExecutedWork.groupFailure_withPublishedProducer
    {work : Execution.Work} (generated : ExecutedWork work)
    {groups streams events matching failures node dependencies producer}
    (explained : Explains work groups streams events matching failures)
    (known : NodeAt work node .group dependencies (some producer))
    (published : Published matching events producer)
    (failure : NodeFailed work matching events failures node.key)
    : (∃ occurrence owners,
        TaskHasOwners work occurrence owners
        ∧ node.key ∈ owners
        ∧ occurrence ∈ failedBefore failures events.length)
      ∨ ∃ dependency ∈ dependencies,
          NodeFailed work matching events failures dependency := by
  have snapshot := explained.nodeFailed_snapshot failure
  cases snapshot with
  | task task owner member => exact .inl ⟨_, _, task, owner, member⟩
  | @groupDependency key otherDependencies dependency descriptor member prior =>
      obtain ⟨other, birth, otherKnown, keyEq⟩ := descriptor
      obtain ⟨parents, canonical⟩ := generated.groupDependenciesCanonical
      have dependenciesEq := canonical node dependencies (some producer) known
      have otherEq := canonical other otherDependencies birth otherKnown
      have same : otherDependencies = dependencies := by
        rw [keyEq] at otherEq
        exact otherEq.trans dependenciesEq.symm
      exact .inr ⟨dependency, same ▸ member, explained.snapshot_nodeFailed prior⟩
  | @streamDependencies key otherDependencies descriptor _ _ =>
      obtain ⟨stream, birth, streamKnown, keyEq⟩ := descriptor
      exact False.elim (generated.groupStreamKeysDisjoint known streamKnown keyEq.symm)
  | producers _ _ unpublished _ =>
      exact False.elim
        (unpublished producer ⟨node, .group, dependencies, known, rfl⟩ published)

/-- A published producer protects its healthy generated child group from later
unrelated failures. Witness: the preceding failure decomposition; neither a failed
contributor nor a failed defer ancestor is available.
-/
theorem ExecutedWork.publishedProducer_groupHealthy
    {work : Execution.Work} (generated : ExecutedWork work)
    {groups streams events matching failures node dependencies producer}
    (explained : Explains work groups streams events matching failures)
    (known : NodeAt work node .group dependencies (some producer))
    (published : Published matching events producer)
    (contributors
      : ∀ occurrence owners,
          TaskHasOwners work occurrence owners
          → node.key ∈ owners
          → occurrence ∉ failedBefore failures events.length)
    (ancestors : ∀ key ∈ dependencies, ¬NodeFailed work matching events failures key)
    : ¬NodeFailed work matching events failures node.key := by
  intro failure
  rcases generated.groupFailure_withPublishedProducer explained known published failure
      with ⟨occurrence, owners, task, owner, failed⟩ | ⟨key, member, failed⟩
  · exact contributors occurrence owners task owner failed
  · exact ancestors key member failed

/-- A root defer group without ancestors can fail only through one of its
contributing task failures. This is the base case for the queue's causal
root-health proof. -/
private theorem ExecutedWork.rootGroupFailure_hasTask
    {work : Execution.Work} (generated : ExecutedWork work)
    {node : Execution.DeliveryNode}
    (root : NodeAt work node .group [] none)
    {matching events failures}
    (failure : NodeFailed work matching events failures node.key)
    : ∃ occurrence owners,
        TaskHasOwners work occurrence owners
        ∧ node.key ∈ owners
        ∧ occurrence ∈ failedBefore failures events.length := by
  rcases generated.groupFailure_withRootProducer root failure with direct
    | ⟨dependency, member, _⟩
  · exact direct
  · cases member

/-- Every recorded defer ancestor has a strictly smaller generated key. In
particular, following child links cannot form a cycle. -/
theorem ExecutedWork.groupAncestorSmaller
    {work : Execution.Work} (generated : ExecutedWork work)
    {node : Execution.DeliveryNode} {dependencies : Keys}
    {producer : Option Occurrence}
    (known : NodeAt work node .group dependencies producer)
    {ancestor : Nat} (member : ancestor ∈ dependencies)
    : ancestor < node.key := by
  obtain ⟨parents, bound, valid, canonical⟩ := generated.groupDependenciesValid
  obtain ⟨keyBound, dependenciesEq⟩ := canonical node dependencies producer known
  rw [dependenciesEq] at member
  exact (valid node.key keyBound ancestor member).1

/-- Every ancestor of a generated defer ancestor is also an ancestor of the child.
Witness: the coherent full ancestor lists satisfy execution's transitive assignment.
-/
theorem ExecutedWork.groupAncestors_trans
    {work : Execution.Work} (generated : ExecutedWork work)
    {node ancestor : Execution.DeliveryNode}
    {dependencies ancestorDependencies : Keys} {producer ancestorProducer}
    (known : NodeAt work node .group dependencies producer)
    (ancestorKnown : NodeAt work ancestor .group ancestorDependencies ancestorProducer)
    (member : ancestor.key ∈ dependencies)
    : ancestorDependencies.Subset dependencies := by
  obtain ⟨parents, bound, valid, canonical⟩ := generated.groupDependenciesValid
  obtain ⟨keyBound, dependenciesEq⟩ := canonical node dependencies producer known
  have ancestorEq := (canonical ancestor ancestorDependencies ancestorProducer
    ancestorKnown).2
  rw [dependenciesEq] at member ⊢
  rw [ancestorEq]
  exact (valid node.key keyBound ancestor.key member).2

/-- Lowering any located child work preserves the generated defer-parent
assignment in each registered GraphQL.js-shaped group descriptor. -/
theorem workFromSpec_groups_parentCanonical
    {root current : Execution.Work} {address : Address}
    {producer : Option Occurrence} {owners : Keys}
    {parents : Nat → Keys}
    (located : Located root address current producer owners)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt root node dependencies → dependencies = parents node.key)
    {group : Group} (member : group ∈ (Work.fromExecution current address).groups)
    : group.parent = (parents group.node.key).head? := by
  obtain ⟨dependencies, known, parent⟩ := workFromSpec_groups_recordAt located member
  rw [parent, canonical _ _ known]

/-- Generated ancestry identifies contributor and ancestor-only registration records.
Witness: execution's exact chain assignment and the descriptor's suffix certificate.
-/
theorem ExecutedWork.groupRecordsValid {work : Execution.Work}
    (generated : ExecutedWork work)
    : ∃ (parents : Nat → Keys) (bound : Nat),
        AncestorChains.Valid parents bound
        ∧ ∀ node dependencies,
            GroupRecordAt work node dependencies
            → node.key < bound ∧ dependencies = parents node.key := by
  obtain ⟨ObjectRef, schema, resolvers, variables, fuel, parentType, source,
    selections, equal⟩ := generated
  obtain ⟨_, parents, valid, coherent⟩ := AncestorChains.executeRoot_chains
    schema resolvers variables fuel parentType source selections 0
  refine ⟨parents, _, valid, ?_⟩
  intro node dependencies known
  obtain ⟨address, groups, path, result, children, producer, owners, fragment,
    ancestors, located, member, suffix, dependenciesEq⟩ := known
  have rootAt := equal ▸ coherent
  have localWork := coherent_located rootAt located
  rw [Semantics.MixedKeys.WorkAt] at localWork
  have fragmentAt := (localWork.2.1 fragment member).2
  rw [dependenciesEq]
  exact ancestor_suffix_canonical valid fragmentAt.1 fragmentAt.2 suffix

/-- All generated registration records share one full-ancestor assignment.
Witness: project the bounded chain certificate, including ancestor-only records.
-/
theorem ExecutedWork.groupRecordsCanonical
    {work : Execution.Work} (generated : ExecutedWork work)
    : ∃ parents : Nat → Keys,
        ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.key := by
  obtain ⟨parents, _, _, canonical⟩ := generated.groupRecordsValid
  exact ⟨parents, fun node dependencies known => (canonical node dependencies known).2⟩

/-- Registration parents have strictly smaller keys, including taskless ancestors.
Witness: the generated bounded assignment orders every key in each ancestry list.
-/
theorem ExecutedWork.groupRecordAncestorSmaller
    {work : Execution.Work} (generated : ExecutedWork work)
    {node dependencies ancestor} (known : GroupRecordAt work node dependencies)
    (member : ancestor ∈ dependencies)
    : ancestor < node.key := by
  obtain ⟨parents, bound, valid, canonical⟩ := generated.groupRecordsValid
  obtain ⟨nodeBound, equal⟩ := canonical node dependencies known
  rw [equal] at member
  exact (valid.1 node.key nodeBound ancestor member).1

/-- A matched task success reveals only contributor or ancestor registration records.
Witness: exact child lowering and its full-chain structural provenance.
-/
theorem GraphEvent.MatchesWork.taskChildGroups_recordAt
    {work : Execution.Work} {occurrence : Occurrence} {result : TaskResult}
    (matching : (GraphEvent.taskSuccess occurrence result).MatchesWork work)
    {group : Group} (member : group ∈ result.work.groups)
    : ∃ dependencies, GroupRecordAt work group.node dependencies := by
  obtain ⟨owners, producer, known, _, childrenWork⟩ := matching
  cases occurrence with
  | item address index =>
      simp only [taskChildWork?] at childrenWork
      cases childrenWork
  | executionGroup address =>
      obtain ⟨groups, path, outcome, children, enclosing,
        located, _, _⟩ := known
      change locateWork work address = some
        ⟨.executionGroup groups path outcome children, producer, enclosing⟩
        at located
      have childLowering : result.work =
          Work.fromExecution children (address ++ [0]) := by
        simpa [taskChildWork?, located] using childrenWork.symm
      rw [childLowering] at member
      have childLocated : Located work (address ++ [0]) children
          (some (.executionGroup address))
          (groups.map (fun group => group.node.key)) :=
        WorkQueueSemantics.Located.executionGroup located
      obtain ⟨dependencies, knownChild, _⟩ :=
        workFromSpec_groups_recordAt childLocated member
      exact ⟨dependencies, knownChild⟩

/-- A matched stream item has the same full-chain registration provenance.
Witness: resolve its child work and apply the structural lowering certificate.
-/
theorem GraphEvent.MatchesWork.streamItem_childGroups_recordAt
    {work : Execution.Work} {stream : Execution.DeliveryNode} {items : List StreamItem}
    (matching : (GraphEvent.streamItems stream items).MatchesWork work)
    {item : StreamItem} (itemMember : item ∈ items)
    {group : Group} (groupMember : group ∈ item.work.groups)
    : ∃ dependencies, GroupRecordAt work group.node dependencies := by
  cases item with
  | mk itemOccurrence itemValue itemWork =>
      obtain ⟨owners, producer, known, childrenWork⟩ := matching _ itemMember
      cases itemOccurrence with
      | executionGroup address =>
          simp only [streamItemWork?] at childrenWork
          cases childrenWork
      | item address index =>
          obtain ⟨node, entries, enclosing, result, children, located, entry,
            _, _⟩ := known
          change locateWork work address = some
            ⟨.stream node entries, producer, enclosing⟩ at located
          have childLowering : itemWork =
              Work.fromExecution children (address ++ [index]) := by
            simpa [streamItemWork?, located, entry] using childrenWork.symm
          rw [childLowering] at groupMember
          have childLocated : Located work (address ++ [index]) children
              (some (.item address index)) [] :=
            WorkQueueSemantics.Located.item located entry
          obtain ⟨dependencies, knownChild, _⟩ :=
            workFromSpec_groups_recordAt childLocated groupMember
          exact ⟨dependencies, knownChild⟩

/-- The same generated defer key cannot lower with two different primary
parents, even when shared execution repeats its group descriptor. -/
private theorem ExecutedWork.loweredGroupParentUnique
    {work first second : Execution.Work}
    {firstAddress secondAddress : Address}
    {firstProducer secondProducer : Option Occurrence}
    {firstOwners secondOwners : Keys}
    (generated : ExecutedWork work)
    (firstLocated : Located work firstAddress first firstProducer firstOwners)
    (secondLocated : Located work secondAddress second secondProducer secondOwners)
    {firstGroup secondGroup : Group}
    (firstMember : firstGroup ∈ (Work.fromExecution first firstAddress).groups)
    (secondMember : secondGroup ∈ (Work.fromExecution second secondAddress).groups)
    (sameKey : firstGroup.node.key = secondGroup.node.key)
    : firstGroup.parent = secondGroup.parent := by
  obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
  have firstParent :=
    workFromSpec_groups_parentCanonical firstLocated canonical firstMember
  have secondParent :=
    workFromSpec_groups_parentCanonical secondLocated canonical secondMember
  rw [firstParent, secondParent, sameKey]

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
