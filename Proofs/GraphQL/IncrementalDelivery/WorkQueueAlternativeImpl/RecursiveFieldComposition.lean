import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.LiteralObjectRefinement

/-! General recursive field composition. The child obligation concerns actual value
completion at arbitrary mapped supplies, not literal resolver values or independently
paired outputs. Original lookup, coercion and resolution select that child. The sibling
driver then constructs one final map for every retained value and Work component. -/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.ScheduledWork

open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Semantics
open GraphQL.IncrementalDelivery.Semantics.RefRegions
open KeyRenaming ScheduledErrors

attribute [local simp] id_pure_eq id_bind_eq id_map_eq run_bind run_map

-----------------------------------------------------------------------------------------
-- Exact recursive roots and inherited input metadata
-----------------------------------------------------------------------------------------

def FieldsBefore (bound : Nat) (fields : CollectedFieldsMap) : Prop :=
  GroupsSatisfy (fun details => UsageBefore bound details.deferUsage) fields

theorem FieldsBefore.mono {left right : Nat} {fields : CollectedFieldsMap}
    (known : FieldsBefore left fields) (advanced : left ≤ right)
    : FieldsBefore right fields :=
  fun entry member details inFields =>
    usageBefore_mono _ (known entry member details inFields) advanced

theorem FieldsBefore.below {bound : Nat} {fields : CollectedFieldsMap}
    (known : FieldsBefore bound fields)
    : FieldsBelow bound fields :=
  fun entry member details inFields =>
    usageBefore_fieldKeys details (known entry member details inFields)

/-- The value-construction root for one fuel. Input conditions describe allocated
metadata, not execution outputs. One existential relates counts, recursive Work, hidden
stream-item keys and both actual final supplies. -/
def ValueRunConstruction (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues) (fuel : Nat)
    : Prop :=
  ∀ fieldType fields (value : ResolverValue ObjectRef) path usages context allowStream
    keys left right,
    SupplyMap keys left right
    → (∀ details ∈ fields, UsageBefore left details.deferUsage)
    → (∀ key ∈ usages, key < left)
    → (∀ key ∈ context.flatMap RefRoles.fragmentRefs, key < left)
    → ∃ next,
        RunRefines keys next left right
          ((ScheduledExecution.completeValue schema resolvers variables fuel fieldType
              fields value path usages context allowStream).run
            left)
          ((Execution.completeValue schema resolvers variables fuel fieldType
              (fields.map (field keys)) value path (usages.map keys)
              (context.map (fragment keys)) allowStream).run
            right)

def FieldScopeRunConstruction (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues) (fuel : Nat)
    : Prop :=
  ∀ parentType (source : ResolverValue ObjectRef) fields path usages context keys left
    right,
    SupplyMap keys left right
    → FieldsBefore left fields
    → (∀ key ∈ usages, key < left)
    → (∀ key ∈ context.flatMap RefRoles.fragmentRefs, key < left)
    → ∃ next,
        RunRefines keys next left right
          ((ScheduledExecution.executeCollectedFields schema resolvers variables fuel
              parentType source fields path usages context).run
            left)
          ((Execution.executeCollectedFields schema resolvers variables fuel parentType
              source (KeyRenaming.fields keys fields) path (usages.map keys)
              (context.map (fragment keys))).run
            right)

-----------------------------------------------------------------------------------------
-- Result wrappers do not allocate identities or change the constructed map
-----------------------------------------------------------------------------------------

theorem pureResult_run {keys : Nat → Nat} {left right : Nat}
    (supplies : SupplyMap keys left right) (result : Result α)
    (cause
      : Option Nat :=
        match result with
        | .error errors => some errors
        | .ok _ => none)
    : RunRefines keys keys left right
        ((Pure.pure ({ result, cause } : Completion α) : StateM Nat (Completion α)).run
          left)
        ((Pure.pure ({ result, cause } : Completion α) : StateM Nat (Completion α)).run
          right) := by
  refine ⟨fun _ _ => rfl, supplies, Nat.le_refl _, Nat.le_refl _, ?_, ?_⟩
  · simp [StateT.run_pure, allRefs, rootRefs, hiddenRegions]
  · exact ⟨ResultRefines.refl _, .empty, rfl⟩

theorem RunRefines.nonNull {initial next left right}
    {scheduled eager : Completion ResponseValue × Nat}
    (known : RunRefines initial next left right scheduled eager)
    : RunRefines initial next left right (scheduled.1.nonNull, scheduled.2)
        (eager.1.nonNull, eager.2) := by
  refine ⟨known.compatible, known.supplies, known.scheduledMonotone, known.eagerMonotone,
    ?_, known.completion.nonNull⟩
  unfold Completion.nonNull
  split
  · simp [Completion.error, allRefs, rootRefs, hiddenRegions]
  · exact known.bounded

-----------------------------------------------------------------------------------------
-- Actual field lookup/coercion/resolution reduces to its selected recursive child
-----------------------------------------------------------------------------------------

theorem responseField_run_of_values (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues) (fuel : Nat)
    (children : ValueRunConstruction schema resolvers variables (fuel - 1))
    (parentType : Name) (source : ResolverValue ObjectRef) (name : Name)
    (fields : List FieldDetails) (path : ResponsePath) (usages : List Nat)
    (context : DeferMap) (keys : Nat → Nat) (left right : Nat)
    (supplies : SupplyMap keys left right)
    (ordered : ∀ details ∈ fields, UsageBefore left details.deferUsage)
    (usageBound : ∀ key ∈ usages, key < left)
    (contextBound : ∀ key ∈ context.flatMap RefRoles.fragmentRefs, key < left)
    : ∃ next,
        RunRefines keys next left right
          ((ScheduledExecution.executeResponseField schema resolvers variables fuel
              parentType source name fields path usages context).run
            left)
          ((Semantics.executeResponseField schema resolvers variables fuel parentType
              source name (fields.map (field keys)) path (usages.map keys)
              (context.map (fragment keys))).run
            right) := by
  cases fuel with
  | zero =>
      exact ⟨
        keys,
        by
          simpa only [ScheduledExecution.executeResponseField,
            Semantics.executeResponseField, Completion.error]
            using pureResult_run supplies (.error 1)
      ⟩
  | succ fuel =>
      simp only [Nat.add_sub_cancel] at children
      cases fields with
      | nil =>
          exact ⟨
            keys,
            by
              simpa only [ScheduledExecution.executeResponseField,
                Semantics.executeResponseField, List.map_nil, Completion.error]
                using pureResult_run supplies (.error 1)
          ⟩
      | cons head tail =>
          simp only [ScheduledExecution.executeResponseField, Semantics.executeResponseField,
            List.map_cons, field]
          split
          · simp_all only
            exact ⟨keys, pureResult_run supplies _ _⟩
          · rename_i definition _
            simp_all only
            split
            · simp_all only
              exact ⟨keys, pureResult_run supplies _ _⟩
            · rename_i arguments _
              simp_all only
              split
              · simp_all only
                exact ⟨keys, pureResult_run supplies _ _⟩
              · rename_i resolved _
                simp_all only
                obtain ⟨next, child⟩ := children definition.outputType (head :: tail) resolved
                  (path ++ [.field name]) usages context true keys left right supplies
                  ordered usageBound contextBound
                refine ⟨next, ?_⟩
                simpa only [List.map_cons, field, run_bind, StateT.run_pure, id_pure_eq]
                  using child.map (fun value => [(name, value)])

-----------------------------------------------------------------------------------------
-- Sibling composition preserves fixed input metadata as each recursive map grows
-----------------------------------------------------------------------------------------

theorem fieldActions_growing_of_values (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues) (fuel : Nat)
    (children : ValueRunConstruction schema resolvers variables (fuel - 1))
    (parentType : Name) (source : ResolverValue ObjectRef) (fields : CollectedFieldsMap)
    (path : ResponsePath) (usages : List Nat) (context : DeferMap)
    (initial : Nat → Nat) (floor : Nat) (ordered : FieldsBefore floor fields)
    (usageBound : ∀ key ∈ usages, key < floor)
    (contextBound : ∀ key ∈ context.flatMap RefRoles.fragmentRefs, key < floor)
    : PairedGrowingActions (MetadataPrefix initial floor)
        (ScheduledExecution.fieldActions schema resolvers variables fuel parentType source
          fields path usages context)
        (ScheduledErrors.fieldActions schema resolvers variables fuel parentType source
          (KeyRenaming.fields initial fields) path (usages.map initial)
          (context.map (fragment initial))) := by
  induction fields with
  | nil => exact .nil
  | cons entry rest ih =>
      apply PairedGrowingActions.cons
      · intro keys left right supplies prefixKnown
        have mappedFields : entry.2.map (field keys) = entry.2.map (field initial) :=
          List.map_congr_left (fun details member => field_congr details
            (fun key inField => prefixKnown.2 key
              (ordered.below entry (by simp) details member key inField)))
        have mappedUsages : usages.map keys = usages.map initial :=
          List.map_congr_left (fun key member => prefixKnown.2 key (usageBound key member))
        have mappedContext := context_prefix context contextBound prefixKnown.2
        obtain ⟨next, child⟩ := responseField_run_of_values schema resolvers variables fuel
          children parentType source entry.1 entry.2 path usages context keys left right
          supplies (fun details member => usageBefore_mono _
            (ordered entry (by simp) details member) prefixKnown.1)
          (fun key member => Nat.lt_of_lt_of_le (usageBound key member) prefixKnown.1)
          (fun key member => Nat.lt_of_lt_of_le (contextBound key member) prefixKnown.1)
        rw [mappedFields, mappedUsages, mappedContext] at child
        refine ⟨(ScheduledExecution.executeResponseField_positive schema resolvers variables
          fuel parentType source entry.1 entry.2 path usages context left).1,
          next, child, ?_⟩
        refine ⟨Nat.le_trans prefixKnown.1 child.scheduledMonotone, ?_⟩
        intro key earlier
        exact (child.compatible key (Nat.lt_of_lt_of_le earlier prefixKnown.1)).trans
          (prefixKnown.2 key earlier)
      · exact ih (fun entry member => ordered entry (List.mem_cons_of_mem _ member))

theorem fieldScope_run_of_values (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues) (fuel : Nat)
    (children : ValueRunConstruction schema resolvers variables (fuel - 1))
    : FieldScopeRunConstruction schema resolvers variables fuel := by
  intro parentType source fields path usages context keys left right supplies ordered
    usageBound contextBound
  exact executeCollectedFields_growing_of_children schema resolvers variables fuel
    parentType source fields (KeyRenaming.fields keys fields) path usages
    (usages.map keys) context (context.map (fragment keys)) (MetadataPrefix keys left)
    keys left right right
    (fieldActions_growing_of_values schema resolvers variables fuel children parentType
      source fields path usages context keys left ordered usageBound contextBound)
    supplies ⟨Nat.le_refl _, fun _ _ => rfl⟩
    (fun key member => by
      obtain ⟨group, groupMember, inGroup⟩ := List.mem_flatMap.mp member
      obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp groupMember
      have mapped : RefRoles.fragmentRefs (fragment keys original)
          = (RefRoles.fragmentRefs original).map keys := by
        simp [RefRoles.fragmentRefs, fragment, node, List.map_map, Function.comp_def]
      rw [mapped] at inGroup
      obtain ⟨prior, priorMember, rfl⟩ := List.mem_map.mp inGroup
      exact supplies.images prior
        (contextBound prior
          (List.mem_flatMap.mpr ⟨original, originalMember, priorMember⟩)))
    (Nat.le_refl _)

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.ScheduledWork
