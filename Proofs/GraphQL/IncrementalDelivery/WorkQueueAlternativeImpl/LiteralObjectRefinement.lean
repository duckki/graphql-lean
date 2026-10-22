import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.LiteralDeferredPlans
import Proofs.GraphQL.IncrementalDelivery.Semantics.Planning
import Proofs.GraphQL.IncrementalDelivery.Semantics.AncestryPlanning

/-! Actual object completion with literal-valued selected leaves. Collection constructs
fresh usage identities and their bounds; original planning transports the resolver domain
and metadata bounds; actual plan execution constructs the extending Work/count witness.
This closes one object boundary without assuming its collected outputs are related.
RecursiveExecutionConstruction supplies the unrestricted recursive construction. -/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.ScheduledWork

open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Semantics
open GraphQL.IncrementalDelivery.Semantics.RefRegions
open KeyRenaming ScheduledErrors

attribute [local simp] id_pure_eq id_bind_eq id_map_eq run_bind run_map

-----------------------------------------------------------------------------------------
-- Reuse actual collection ordering to bound all field keys, including ancestors
-----------------------------------------------------------------------------------------

theorem usageBefore_fieldKeys {bound : Nat} (details : FieldDetails)
    (known : UsageBefore bound details.deferUsage)
    : ∀ key ∈ fieldKeys details, key < bound := by
  intro key member
  simp only [fieldKeys, List.mem_flatMap, Option.mem_toList] at member
  obtain ⟨usage, inUsage, member⟩ := member
  have before := known usage inUsage
  rcases List.mem_cons.mp member with rfl | ancestor
  · exact before.1
  · exact Nat.lt_trans (before.2 key ancestor) before.1

theorem filtered_keys_below {bound : Nat} (fields : List FieldDetails)
    (known : ∀ details ∈ fields, ∀ key ∈ fieldKeys details, key < bound)
    : ∀ key ∈ getFilteredDeferUsageSet fields, key < bound := by
  intro key member
  obtain ⟨details, inFields, usage, actual, rfl⟩ := Ancestry.filtered_ref_source fields key member
  exact known details inFields usage.ref (by simp [fieldKeys, actual])

private theorem add_partition_below {bound : Nat} (usages : List Nat)
    (group : Name × List FieldDetails) (partitions : List (List Nat × CollectedFieldsMap))
    (fresh : ∀ key ∈ usages, key < bound)
    (known : ∀ partition ∈ partitions, ∀ key ∈ partition.1, key < bound)
    : ∀ partition ∈ addExecutionPartition usages group partitions,
      ∀ key ∈ partition.1, key < bound := by
  induction partitions with
  | nil =>
      intro partition member
      simp only [addExecutionPartition, List.mem_singleton] at member
      subst partition
      exact fresh
  | cons head rest ih =>
      rcases head with ⟨keys, fields⟩
      simp only [addExecutionPartition]
      split
      · intro partition member key inKeys
        rcases List.mem_cons.mp member with rfl | member
        · exact known (keys, fields) (by simp) key inKeys
        · exact known partition (List.mem_cons_of_mem _ member) key inKeys
      · intro partition member key inKeys
        rcases List.mem_cons.mp member with rfl | member
        · exact known (keys, fields) (by simp) key inKeys
        · exact ih (fun partition member => known partition (List.mem_cons_of_mem _ member))
            partition member key inKeys

theorem build_plan_below {bound : Nat} (fields : CollectedFieldsMap) (parent : List Nat)
    (known : FieldsBelow bound fields)
    : FieldsBelow bound (buildExecutionPlan fields parent).collectedFieldsMap
      ∧ PartitionsBelow bound
          (buildExecutionPlan fields parent).newCollectedFieldsMaps := by
  have fieldBounds := buildExecutionPlan_preserves_property
    (fun details => ∀ key ∈ fieldKeys details, key < bound) fields parent known
  have usageBounds : ∀ partition ∈ (buildExecutionPlan fields parent).newCollectedFieldsMaps,
      ∀ key ∈ partition.1, key < bound := by
    clear fieldBounds
    suffices ∀ initial : ExecutionPlan,
        (∀ partition ∈ initial.newCollectedFieldsMaps, ∀ key ∈ partition.1, key < bound)
        → ∀ partition ∈ (fields.foldl
            (fun plan group =>
              let usages := getFilteredDeferUsageSet group.2
              if deferUsageSetsEquivalent usages parent then
                { plan with collectedFieldsMap := plan.collectedFieldsMap ++ [group] }
              else { plan with newCollectedFieldsMaps :=
                addExecutionPartition usages group plan.newCollectedFieldsMaps }) initial).newCollectedFieldsMaps,
            ∀ key ∈ partition.1, key < bound by
      exact this {} (by simp)
    intro initial initialBound
    induction fields generalizing initial with
    | nil => exact initialBound
    | cons group rest ih =>
        simp only [List.foldl_cons]
        apply ih (fun entry member => known entry (List.mem_cons_of_mem _ member))
        split
        · exact initialBound
        · exact add_partition_below _ _ _
            (filtered_keys_below group.2 (known group (by simp))) initialBound
  exact ⟨fieldBounds.1, fun partition member =>
    ⟨usageBounds partition member, fieldBounds.2 partition member⟩⟩

theorem build_plan_literal (resolvers : Resolvers ObjectRef) (parentType : Name)
    (source : ResolverValue ObjectRef) (fields : CollectedFieldsMap) (parent : List Nat)
    (literal : LiteralFields resolvers parentType source fields)
    : LiteralFields resolvers parentType source
        (buildExecutionPlan fields parent).collectedFieldsMap
      ∧ LiteralPartitions resolvers parentType source
          (buildExecutionPlan fields parent).newCollectedFieldsMaps := by
  exact buildExecutionPlan_preserves_property
    (fun details => ∀ arguments value,
      resolveFieldValue resolvers parentType details.fieldName arguments source = some value
      → LiteralValue value) fields parent literal

theorem SupplyMap.orderedBoundary {keys : Nat → Nat} {left right finish : Nat}
    (known : SupplyMap keys left right) (advanced : left ≤ finish)
    : right ≤ keys finish := by
  have actual := known.fresh (finish - left)
  rw [Nat.add_sub_of_le advanced, known.boundary] at actual
  omega

-----------------------------------------------------------------------------------------
-- Construct one completeValue object witness from its actual collection and plan
-----------------------------------------------------------------------------------------

theorem literal_object_run (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues) (fuel : Nat) (parentType runtimeType : Name)
    (reference : ObjectRef) (fields : List FieldDetails) (path : ResponsePath)
    (usages : List Nat) (context : DeferMap) (allowStream : Bool) (keys : Nat → Nat)
    (left right : Nat) (supplies : SupplyMap keys left right)
    (inherited : ∀ details ∈ fields, UsageBefore left details.deferUsage)
    (usageBound : ∀ key ∈ usages, key < left)
    (contextBound : ∀ key ∈ context.flatMap RefRoles.fragmentRefs, key < left)
    (literal
      : LiteralFields resolvers runtimeType (.object runtimeType reference)
          ((collectSubfields schema variables runtimeType (.object runtimeType reference)
              fields).run
            left).1.collectedFieldsMap)
    : ∃ next,
        RunRefines keys next left right
          ((ScheduledExecution.completeValue schema resolvers variables (fuel + 1)
              (.named parentType) fields (.object runtimeType reference) path usages
              context allowStream).run
            left)
          ((Execution.completeValue schema resolvers variables (fuel + 1)
              (.named parentType) (fields.map (field keys))
              (.object runtimeType reference) path (usages.map keys)
              (context.map (fragment keys)) allowStream).run
            right) := by
  cases includes : schema.typeIncludesObjectBool parentType runtimeType with
  | false =>
      simp only [ScheduledExecution.completeValue, Execution.completeValue, includes,
        Bool.not_false, ↓reduceIte, StateT.run_pure, id_pure_eq]
      refine ⟨keys, ⟨fun _ _ => rfl, supplies, Nat.le_refl _, Nat.le_refl _, ?_, ?_⟩⟩
      · simp [Completion.error, allRefs, rootRefs, hiddenRegions]
      · exact CompletionRefines.error (ResultRefines.refl _) rfl
  | true =>
      let collected := (collectSubfields schema variables runtimeType
        (.object runtimeType reference) fields).run left
      have collectedKeys := collectSubfields_refs schema variables runtimeType
        (.object runtimeType reference) fields left inherited
      have collectedFields : FieldsBelow collected.2 collected.1.collectedFieldsMap :=
        fun entry member details inFields => usageBefore_fieldKeys details
          (collectedKeys.2.1 entry member details inFields)
      have plannedBounds := build_plan_below collected.1.collectedFieldsMap usages collectedFields
      have plannedLiteral := build_plan_literal resolvers runtimeType (.object runtimeType reference)
        collected.1.collectedFieldsMap usages literal
      have afterContext : ∀ key ∈ (getNewDeferMap collected.1.newDeferUsages path context).flatMap
          RefRoles.fragmentRefs, key < collected.2 :=
        mapRefs_new_bound context collected.1.newDeferUsages path collected.2
          (fun key member => Nat.lt_of_lt_of_le (contextBound key member) collectedKeys.1)
          (fun usage member => (collectedKeys.2.2 usage member).2.1)
      obtain ⟨next, planned⟩ := literal_executeExecutionPlan_run schema resolvers variables fuel
        runtimeType (.object runtimeType reference) collected.1.newDeferUsages
        (buildExecutionPlan collected.1.collectedFieldsMap usages) path usages context keys
        collected.2 (keys collected.2) plannedLiteral.1 plannedLiteral.2
        (supplies.advance collectedKeys.1) plannedBounds.1 plannedBounds.2
        (fun key member => Nat.lt_of_lt_of_le (usageBound key member) collectedKeys.1) afterContext
      have collectedMapped := collectSubfields_maps keys schema variables runtimeType
        (.object runtimeType reference) fields left supplies.fresh
      rw [supplies.boundary] at collectedMapped
      simp only [ScheduledExecution.completeValue, Execution.completeValue, includes,
        Bool.not_true, Bool.false_eq_true, ↓reduceIte, run_bind, collectedMapped,
        collection, build_plan supplies.injective, StateT.run_pure, id_pure_eq]
      have caught := planned.catchNull ResponseValue.object
      refine ⟨next, ⟨?_, caught.supplies,
        Nat.le_trans collectedKeys.1 caught.scheduledMonotone,
        Nat.le_trans (supplies.orderedBoundary collectedKeys.1) caught.eagerMonotone,
        caught.bounded, caught.completion⟩⟩
      intro key earlier
      exact caught.compatible key (Nat.lt_of_lt_of_le earlier collectedKeys.1)

/-- An actual object boundary with literal-valued selected leaves constructs its full
recursive Work/count map. Input ancestry is ordered/bounded; collection and planning
derive all new metadata bounds rather than assuming related collected outputs. -/
def LiteralObjectCompletionRefinement : Prop :=
  ∀ (ObjectRef : Type) (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues) fuel parentType runtimeType (reference : ObjectRef)
    fields path usages context allowStream keys left right,
    SupplyMap keys left right
    → (∀ details ∈ fields, UsageBefore left details.deferUsage)
    → (∀ key ∈ usages, key < left)
    → (∀ key ∈ context.flatMap RefRoles.fragmentRefs, key < left)
    → LiteralFields resolvers runtimeType (.object runtimeType reference)
        ((collectSubfields schema variables runtimeType (.object runtimeType reference)
            fields).run
          left).1.collectedFieldsMap
    → ∃ next,
        RunRefines keys next left right
          ((ScheduledExecution.completeValue schema resolvers variables (fuel + 1)
              (.named parentType) fields (.object runtimeType reference) path usages
              context allowStream).run
            left)
          ((Execution.completeValue schema resolvers variables (fuel + 1)
              (.named parentType) (fields.map (field keys))
              (.object runtimeType reference) path (usages.map keys)
              (context.map (fragment keys)) allowStream).run
            right)

theorem literalObjectCompletionRefinement_holds : LiteralObjectCompletionRefinement := by
  intro ObjectRef schema resolvers variables fuel parentType runtimeType reference fields path
    usages context allowStream keys left right supplies inherited usageBound contextBound literal
  exact literal_object_run schema resolvers variables fuel parentType runtimeType reference fields
    path usages context allowStream keys left right supplies inherited usageBound contextBound literal

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.ScheduledWork
