import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.LiteralExecutionTransport
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.ScheduledKeyRegions

/-! Constructed literal field children at mapped supplies, and their real sibling
driver. Later cuts preserve the inherited metadata prefix; no paired-child or output
correspondence premise is supplied by callers. General object-valued children remain
outside the literal resolver domain. -/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.ScheduledWork

open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Semantics
open GraphQL.IncrementalDelivery.Semantics.RefRegions
open KeyRenaming ScheduledErrors

attribute [local simp] id_pure_eq id_bind_eq id_map_eq run_bind run_map

-----------------------------------------------------------------------------------------
-- Change only the eager side, transporting retained counts and recursive Work
-----------------------------------------------------------------------------------------

theorem WorkRefines.renameRight {keys : Nat → Nat} {left right : Work}
    (known : WorkRefines keys left right) (rename : Nat → Nat)
    : WorkRefines (rename ∘ keys) left (work rename right) := by
  induction known
    using WorkRefines.rec
      (motive_2 :=
        fun left right _ =>
          ItemsRefine (rename ∘ keys) left
            (right.map (fun item => (item.1, work rename item.2)))) with
  | empty => simpa only [work] using WorkRefines.empty (keys := rename ∘ keys)
  | combine head tail ihHead ihTail =>
      simpa only [work] using WorkRefines.combine ihHead ihTail
  | executionGroup payload nested ih =>
      simpa only [work, List.map_map, fragment_comp, Function.comp_def]
        using WorkRefines.executionGroup (keys := rename ∘ keys) payload ih
  | stream nested ih =>
      simpa only [work, node_comp] using WorkRefines.stream (keys := rename ∘ keys) ih
  | nil => exact .nil
  | cons payload nested tail ihHead ihTail => exact .cons payload ihHead ihTail

theorem CompletionRefines.renameRight {keys : Nat → Nat} {left right : Completion α}
    (known : CompletionRefines keys left right) (rename : Nat → Nat)
    : CompletionRefines (rename ∘ keys) left (completion rename right) :=
  ⟨known.1, known.2.1.renameRight rename, known.2.2⟩

-----------------------------------------------------------------------------------------
-- Original field lookup/coercion/resolution branches transport actual literal runs
-----------------------------------------------------------------------------------------

theorem literal_responseField_maps (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues) (fuel : Nat) (parentType : Name)
    (source : ResolverValue ObjectRef) (name : Name) (fields : List FieldDetails)
    (path : ResponsePath) (usages : List Nat) (context : DeferMap)
    (literal : LiteralFieldValues resolvers parentType source fields)
    (keys : Nat → Nat) (start : Nat) (fresh : FreshTail keys start)
    : (Semantics.executeResponseField schema resolvers variables fuel parentType source
        name (fields.map (field keys)) path (usages.map keys)
        (context.map (fragment keys))).run
        (keys start)
      = (
        completion keys
          ((Semantics.executeResponseField schema resolvers variables fuel parentType
              source name fields path usages context).run
            start).1,
        keys
          ((Semantics.executeResponseField schema resolvers variables fuel parentType
              source name fields path usages context).run
            start).2
      ) := by
  cases fuel with
  | zero => simp [Semantics.executeResponseField, completion, Completion.error, work]
  | succ fuel =>
      cases fields with
      | nil => simp [Semantics.executeResponseField, completion, Completion.error, work]
      | cons head tail =>
          simp only [Semantics.executeResponseField, List.map_cons, field]
          split
          · simp [completion, Completion.error, work]
          · rename_i definition _
            split
            · simp [completion, work]
            · rename_i arguments _
              split
              · simp [completion, work]
              · rename_i resolved actual
                have transported := literal_value_maps schema resolvers variables fuel definition.outputType
                  (head :: tail) resolved (path ++ [.field name]) usages context true
                  (literal head (by simp) arguments resolved actual) keys start fresh
                simp only [List.map_cons, field] at transported
                simp only [run_bind, transported, StateT.run_pure, id_pure_eq, completion_map]

/-- One actual literal field constructs its full run certificate at arbitrary paired
supplies. Its map is unchanged; only its caller's fatal suffix can extend the map. -/
theorem literal_responseField_run (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues) (fuel : Nat) (parentType : Name)
    (source : ResolverValue ObjectRef) (name : Name) (fields : List FieldDetails)
    (path : ResponsePath) (usages : List Nat) (context : DeferMap)
    (literal : LiteralFieldValues resolvers parentType source fields)
    (keys : Nat → Nat) (left right : Nat) (supplies : SupplyMap keys left right)
    (inherited : ∀ key ∈ context.flatMap RefRoles.fragmentRefs, key < left)
    : RunRefines keys keys left right
        ((ScheduledExecution.executeResponseField schema resolvers variables fuel
            parentType source name fields path usages context).run
          left)
        ((Semantics.executeResponseField schema resolvers variables fuel parentType source
            name (fields.map (field keys)) path (usages.map keys)
            (context.map (fragment keys))).run
          right) := by
  obtain ⟨related, sameSupply⟩ := literal_executeResponseField_refines schema resolvers
    variables fuel parentType source name fields path usages context literal left
  have transported := literal_responseField_maps schema resolvers variables fuel parentType
    source name fields path usages context literal keys left supplies.fresh
  rw [supplies.boundary] at transported
  rw [transported]
  have regions := ScheduledExecution.executeResponseField_regions schema resolvers variables
    fuel parentType source name fields path usages context left inherited
  refine ⟨fun _ _ => rfl, ?_, regions.monotone, ?_, regions.bounded, ?_⟩
  · rw [← sameSupply]
    exact supplies.advance regions.monotone
  · rw [← sameSupply, ← supplies.boundary]
    have fresh := supplies.fresh
    have relation := fresh
      (((ScheduledExecution.executeResponseField schema resolvers variables fuel parentType
        source name fields path usages context).run left).2 - left)
    rw [Nat.add_sub_of_le regions.monotone] at relation
    omega
  · simpa only [Function.comp_def, id_eq] using related.renameRight keys

-----------------------------------------------------------------------------------------
-- Fixed inherited metadata stays mapped while sibling children extend the fresh tail
-----------------------------------------------------------------------------------------

def MetadataPrefix (initial : Nat → Nat) (floor : Nat) (next : Nat → Nat)
    (left _right : Nat)
    : Prop :=
  floor ≤ left ∧ (∀ key < floor, next key = initial key)

def fieldKeys (details : FieldDetails) : List Nat :=
  details.deferUsage.toList.flatMap (fun usage => usage.ref :: usage.ancestors)

theorem field_congr {before after : Nat → Nat} (details : FieldDetails)
    (same : ∀ key ∈ fieldKeys details, after key = before key)
    : field after details = field before details := by
  cases known : details.deferUsage with
  | none => simp [field, known]
  | some usage =>
      have key := same usage.ref (by simp [fieldKeys, known])
      have ancestors : usage.ancestors.map after = usage.ancestors.map before :=
        List.map_congr_left (fun item member => same item (by simp [fieldKeys, known, member]))
      simp only [field, known, Option.map_some, KeyRenaming.usage, key, ancestors]

theorem literal_fieldActions_growing (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues) (fuel : Nat) (parentType : Name)
    (source : ResolverValue ObjectRef) (fields : CollectedFieldsMap)
    (path : ResponsePath) (usages : List Nat) (context : DeferMap)
    (literal : LiteralFields resolvers parentType source fields)
    (initial : Nat → Nat) (floor : Nat)
    (fieldBound
      : ∀ entry ∈ fields, ∀ details ∈ entry.2, ∀ key ∈ fieldKeys details, key < floor)
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
            (fun key inField => prefixKnown.2 key (fieldBound entry (by simp) details member key inField)))
        have mappedUsages : usages.map keys = usages.map initial :=
          List.map_congr_left (fun key member => prefixKnown.2 key (usageBound key member))
        have mappedContext : context.map (fragment keys) = context.map (fragment initial) :=
          List.map_congr_left (fun group member => fragment_congr group
            (fun key inGroup => prefixKnown.2 key
              (contextBound key (List.mem_flatMap.mpr ⟨group, member, inGroup⟩))))
        have child := literal_responseField_run schema resolvers variables fuel parentType
          source entry.1 entry.2 path usages context (literal entry (by simp)) keys left right
          supplies (fun key member => Nat.lt_of_lt_of_le (contextBound key member) prefixKnown.1)
        rw [mappedFields, mappedUsages, mappedContext] at child
        refine ⟨(ScheduledExecution.executeResponseField_positive schema resolvers variables
          fuel parentType source entry.1 entry.2 path usages context left).1,
          keys, child, ?_⟩
        exact ⟨Nat.le_trans prefixKnown.1 child.scheduledMonotone, prefixKnown.2⟩
      · exact ih
          (fun entry member => literal entry (List.mem_cons_of_mem _ member))
          (fun entry member => fieldBound entry (List.mem_cons_of_mem _ member))

/-- Constructed literal field scope with one final map through all retained siblings,
including cuts that skip a later stream. The metadata prefix is bounded explicitly. -/
def LiteralGrowingFieldScope : Prop :=
  ∀ (ObjectRef : Type) (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues) fuel parentType (source : ResolverValue ObjectRef)
    fields path usages context keys left right,
    LiteralFields resolvers parentType source fields
    → SupplyMap keys left right
    → (∀ entry ∈ fields, ∀ details ∈ entry.2, ∀ key ∈ fieldKeys details, key < left)
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

theorem literalGrowingFieldScope_holds : LiteralGrowingFieldScope := by
  intro ObjectRef schema resolvers variables fuel parentType source fields path usages context
    keys left right literal supplies fieldBound usageBound contextBound
  exact executeCollectedFields_growing_of_children schema resolvers variables fuel
    parentType source fields (KeyRenaming.fields keys fields) path usages
    (usages.map keys) context (context.map (fragment keys)) (MetadataPrefix keys left)
    keys left right right
    (literal_fieldActions_growing schema resolvers variables fuel parentType source fields
      path usages context literal keys left fieldBound usageBound contextBound)
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
