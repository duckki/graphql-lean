import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.RecursiveFieldComposition

/-! General ordinary-list and stream-tail composition at growing supplies. Stream
items retain separate recursive Work; the final map preserves all earlier hidden keys.
Both executors already stop the stream tail at the same first fatal item. -/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.ScheduledWork

open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Semantics
open GraphQL.IncrementalDelivery.Semantics.RefRegions
open KeyRenaming ScheduledErrors

attribute [local simp] id_pure_eq id_bind_eq id_map_eq run_bind run_map

-----------------------------------------------------------------------------------------
-- Actual ordinary-list children use one fixed inherited metadata prefix
-----------------------------------------------------------------------------------------

theorem listActions_growing_of_values (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues) (fuel : Nat)
    (children : ValueRunConstruction schema resolvers variables fuel)
    (itemType : TypeRef) (fields : List FieldDetails)
    (values : List (ResolverValue ObjectRef)) (path : ResponsePath) (index : Nat)
    (usages : List Nat) (context : DeferMap) (initial : Nat → Nat) (floor : Nat)
    (ordered : ∀ details ∈ fields, UsageBefore floor details.deferUsage)
    (usageBound : ∀ key ∈ usages, key < floor)
    (contextBound : ∀ key ∈ context.flatMap RefRoles.fragmentRefs, key < floor)
    : PairedGrowingActions (MetadataPrefix initial floor)
        (ScheduledExecution.listActions schema resolvers variables fuel itemType fields
          path usages context values index)
        (ScheduledErrors.listActions schema resolvers variables fuel itemType
          (fields.map (field initial)) path (usages.map initial)
          (context.map (fragment initial)) values index) := by
  induction values generalizing index with
  | nil => exact .nil
  | cons value rest ih =>
      apply PairedGrowingActions.cons
      · intro keys left right supplies prefixKnown
        have mappedFields : fields.map (field keys) = fields.map (field initial) :=
          List.map_congr_left (fun details member => field_congr details
            (fun key inField => prefixKnown.2 key
              (usageBefore_fieldKeys details (ordered details member) key inField)))
        have mappedUsages : usages.map keys = usages.map initial :=
          List.map_congr_left (fun key member => prefixKnown.2 key (usageBound key member))
        have mappedContext := context_prefix context contextBound prefixKnown.2
        obtain ⟨next, child⟩ := children itemType fields value (path ++ [.index index])
          usages context false keys left right supplies
          (fun details member => usageBefore_mono _ (ordered details member) prefixKnown.1)
          (fun key member => Nat.lt_of_lt_of_le (usageBound key member) prefixKnown.1)
          (fun key member => Nat.lt_of_lt_of_le (contextBound key member) prefixKnown.1)
        rw [mappedFields, mappedUsages, mappedContext] at child
        refine ⟨(ScheduledExecution.completeValue_positive schema resolvers variables fuel
          itemType fields value (path ++ [.index index]) usages context false left).1,
          next, child, ?_⟩
        refine ⟨Nat.le_trans prefixKnown.1 child.scheduledMonotone, ?_⟩
        intro key earlier
        exact (child.compatible key (Nat.lt_of_lt_of_le earlier prefixKnown.1)).trans
          (prefixKnown.2 key earlier)
      · exact ih (index + 1)

theorem list_run_of_values (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues) (fuel : Nat)
    (children : ValueRunConstruction schema resolvers variables fuel)
    (itemType : TypeRef) (fields : List FieldDetails)
    (values : List (ResolverValue ObjectRef)) (path : ResponsePath) (index : Nat)
    (usages : List Nat) (context : DeferMap) (keys : Nat → Nat) (left right : Nat)
    (supplies : SupplyMap keys left right)
    (ordered : ∀ details ∈ fields, UsageBefore left details.deferUsage)
    (usageBound : ∀ key ∈ usages, key < left)
    (contextBound : ∀ key ∈ context.flatMap RefRoles.fragmentRefs, key < left)
    : ∃ next,
        RunRefines keys next left right
          ((ScheduledExecution.completeListValue schema resolvers variables fuel itemType
              fields values path index usages context).run
            left)
          ((Execution.completeListValue schema resolvers variables fuel itemType
              (fields.map (field keys)) values path index (usages.map keys)
              (context.map (fragment keys))).run
            right) := by
  exact completeListValue_growing_of_children schema resolvers variables fuel itemType
    fields (fields.map (field keys)) values path index usages (usages.map keys) context
    (context.map (fragment keys)) (MetadataPrefix keys left) keys left right right
    (listActions_growing_of_values schema resolvers variables fuel children itemType
      fields values path index usages context keys left ordered usageBound contextBound)
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

-----------------------------------------------------------------------------------------
-- Item runs retain ordered positions, child Work and their actual supply boundaries
-----------------------------------------------------------------------------------------

structure ItemsRunRefines (initial next : Nat → Nat) (left right : Nat)
    (scheduled eager : List (Result ResponseValue × Work) × Nat)
    : Prop where
  compatible : ∀ key < left, next key = initial key
  supplies : SupplyMap next scheduled.2 eager.2
  scheduledMonotone : left ≤ scheduled.2
  eagerMonotone : right ≤ eager.2
  bounded : ∀ item ∈ scheduled.1, ∀ key ∈ allRefs item.2, key < scheduled.2
  items : ItemsRefine next scheduled.1 eager.1

theorem streamItems_run_of_values (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues) (fuel : Nat)
    (children : ValueRunConstruction schema resolvers variables fuel)
    (itemType : TypeRef) (fields : List FieldDetails)
    (values : List (ResolverValue ObjectRef)) (path : ResponsePath) (index : Nat)
    (keys : Nat → Nat) (left right : Nat) (supplies : SupplyMap keys left right)
    (ordered : ∀ details ∈ fields, UsageBefore left details.deferUsage)
    : ∃ next,
        ItemsRunRefines keys next left right
          ((ScheduledExecution.completeStreamItems schema resolvers variables fuel
              itemType fields values path index).run
            left)
          ((Execution.completeStreamItems schema resolvers variables fuel itemType
              (fields.map (field keys)) values path index).run
            right) := by
  induction values generalizing keys left right index with
  | nil =>
      simp only [ScheduledExecution.completeStreamItems, Execution.completeStreamItems,
        StateT.run_pure, id_pure_eq]
      refine ⟨keys, ⟨fun _ _ => rfl, supplies, Nat.le_refl _, Nat.le_refl _, ?_, .nil⟩⟩
      simp
  | cons value rest ih =>
      obtain ⟨middle, head⟩ := children itemType fields value (path ++ [.index index])
        [] [] false keys left right supplies ordered (by simp) (by simp)
      simp only [List.map_nil] at head
      have same := head.completion.1.1
      simp only [ScheduledExecution.completeStreamItems, Execution.completeStreamItems, run_bind]
      cases cutOutcome :
          ((ScheduledExecution.completeValue schema resolvers variables fuel itemType fields
            value (path ++ [.index index]) [] [] false).run left).1.result
      <;> cases eagerOutcome :
          ((Execution.completeValue schema resolvers variables fuel itemType (fields.map (field keys))
            value (path ++ [.index index]) [] [] false).run right).1.result
      <;> simp only [SameData, cutOutcome, eagerOutcome] at same
      · simp only [StateT.run_pure, id_pure_eq]
        refine ⟨middle, ⟨head.compatible, head.supplies, head.scheduledMonotone,
          head.eagerMonotone, ?_, .cons ?_ .empty .nil⟩⟩
        · simp [allRefs, rootRefs, hiddenRegions]
        · simpa only [cutOutcome, eagerOutcome] using head.completion.1
      · obtain ⟨next, tail⟩ := ih (index + 1) middle _ _ head.supplies
          (fun details member => usageBefore_mono _ (ordered details member) head.scheduledMonotone)
        have fieldsMapped : fields.map (field middle) = fields.map (field keys) :=
          List.map_congr_left (fun details member => field_congr details
            (fun key inField => head.compatible key
              (usageBefore_fieldKeys details (ordered details member) key inField)))
        rw [fieldsMapped] at tail
        simp only [run_bind, StateT.run_pure, id_pure_eq]
        refine ⟨next, ⟨?_, tail.supplies,
          Nat.le_trans head.scheduledMonotone tail.scheduledMonotone,
          Nat.le_trans head.eagerMonotone tail.eagerMonotone, ?_, ?_⟩⟩
        · intro key earlier
          exact (tail.compatible key (Nat.lt_of_lt_of_le earlier head.scheduledMonotone)).trans
            (head.compatible key earlier)
        · intro item member key inWork
          rcases List.mem_cons.mp member with rfl | member
          · exact Nat.lt_of_lt_of_le (head.bounded key inWork) tail.scheduledMonotone
          · exact tail.bounded item member key inWork
        · refine .cons ?_
            (head.completion.2.rekey (fun key member => tail.compatible key (head.bounded key member)))
            tail.items
          simpa only [cutOutcome, eagerOutcome] using head.completion.1

-----------------------------------------------------------------------------------------
-- A stream boundary follows the actual initial scope, before separate item regions
-----------------------------------------------------------------------------------------

theorem RunRefines.withStream {initial middle next left right}
    {scheduled eager : Completion (List ResponseValue) × Nat}
    (known : RunRefines initial middle left right scheduled eager)
    {cutItems eagerItems : List (Result ResponseValue × Work) × Nat}
    (items
      : ItemsRunRefines middle next (scheduled.2 + 1) (eager.2 + 1) cutItems eagerItems)
    (path : ResponsePath) (label : Option DirectiveLabel)
    : RunRefines initial next left right
        (
          {
            (scheduled.1.catchNull ResponseValue.list) with
              work :=
                .combine (scheduled.1.catchNull ResponseValue.list).work
                  (.stream { ref := scheduled.2, path, label } cutItems.1)
          },
          cutItems.2
        )
        (
          {
            (eager.1.catchNull ResponseValue.list) with
              work :=
                .combine (eager.1.catchNull ResponseValue.list).work
                  (.stream { ref := eager.2, path, label } eagerItems.1)
          },
          eagerItems.2
        ) := by
  have caught := known.catchNull ResponseValue.list
  have boundary : next scheduled.2 = eager.2 :=
    (items.compatible scheduled.2 (Nat.lt_succ_self _)).trans known.supplies.boundary
  refine ⟨
    ?_,
    items.supplies,
    Nat.le_trans known.scheduledMonotone (by have := items.scheduledMonotone; omega),
    Nat.le_trans known.eagerMonotone (by have := items.eagerMonotone; omega),
    ?_,
    ?_
  ⟩
  · intro key earlier
    exact (items.compatible key (by have := known.scheduledMonotone; omega)).trans
      (known.compatible key earlier)
  · intro key member
    rcases (mem_allRefs_combine _ _ _).mp member with inInitial | inStream
    · exact Nat.lt_of_lt_of_le (caught.bounded key inInitial)
        (by have := items.scheduledMonotone; omega)
    · simp only [allRefs, rootRefs, hiddenRegions, List.mem_append, List.mem_singleton] at inStream
      rcases inStream with rfl | member
      · exact items.scheduledMonotone
      · obtain ⟨region, inRegions, inRegion⟩ := List.mem_flatten.mp member
        obtain ⟨item, inItems, inRegions⟩ := List.mem_flatMap.mp inRegions
        exact items.bounded item inItems key (region_subset_allRefs item.2 inRegions inRegion)
  · refine ⟨caught.completion.1, .combine ?_ ?_⟩
    · exact caught.completion.2.rekey
        (fun key member => items.compatible key (by have := caught.bounded key member; omega))
    · have nodes : node next { ref := scheduled.2, path, label }
          = { ref := eager.2, path, label } := by simp [node, boundary]
      rw [← nodes]
      exact .stream items.items

theorem mapped_field_directives (keys : Nat → Nat) (fields : List FieldDetails)
    : ((fields.map (field keys)).head?.map FieldDetails.directives).getD []
      = (fields.head?.map FieldDetails.directives).getD [] := by
  cases fields <;> simp [field]

theorem mapped_stream_fields (keys : Nat → Nat) (fields : List FieldDetails)
    : (fields.map (fun details => { details with deferUsage := none })).map (field keys)
      = (fields.map (field keys)).map
          (fun details => { details with deferUsage := none }) := by
  simp [List.map_map, field, Function.comp_def]

theorem listWithStream_run_of_values (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues) (fuel : Nat)
    (children : ValueRunConstruction schema resolvers variables fuel)
    (itemType : TypeRef) (fields : List FieldDetails)
    (values : List (ResolverValue ObjectRef)) (path : ResponsePath)
    (usages : List Nat) (context : DeferMap) (allowStream : Bool)
    (keys : Nat → Nat) (left right : Nat) (supplies : SupplyMap keys left right)
    (ordered : ∀ details ∈ fields, UsageBefore left details.deferUsage)
    (usageBound : ∀ key ∈ usages, key < left)
    (contextBound : ∀ key ∈ context.flatMap RefRoles.fragmentRefs, key < left)
    : ∃ next,
        RunRefines keys next left right
          ((ScheduledExecution.completeListValueWithStream schema resolvers variables fuel
              itemType fields values path usages context allowStream).run
            left)
          ((Execution.completeListValueWithStream schema resolvers variables fuel itemType
              (fields.map (field keys)) values path (usages.map keys)
              (context.map (fragment keys)) allowStream).run
            right) := by
  simp only [ScheduledExecution.completeListValueWithStream, Execution.completeListValueWithStream,
    mapped_field_directives]
  split
  · simp_all only
    exact ⟨keys, pureResult_run supplies _⟩
  · simp_all only
    obtain ⟨next, completed⟩ := list_run_of_values schema resolvers variables fuel children
      itemType fields values path 0 usages context keys left right supplies ordered usageBound contextBound
    exact ⟨next, by simpa only [run_bind, StateT.run_pure, id_pure_eq]
      using completed.catchNull ResponseValue.list⟩
  · rename_i usage actual
    simp only [actual]
    obtain ⟨middle, initialRun⟩ := list_run_of_values schema resolvers variables fuel children
      itemType fields (values.take usage.initialCount) path 0 usages context keys left right
      supplies ordered usageBound contextBound
    have same := initialRun.completion.1.1
    simp only [run_bind]
    cases cutOutcome :
        ((ScheduledExecution.completeListValue schema resolvers variables fuel itemType fields
          (values.take usage.initialCount) path 0 usages context).run left).1.result
    <;> cases eagerOutcome :
        ((Execution.completeListValue schema resolvers variables fuel itemType (fields.map (field keys))
          (values.take usage.initialCount) path 0 (usages.map keys)
          (context.map (fragment keys))).run right).1.result
    <;> simp only [SameData, cutOutcome, eagerOutcome] at same
    · exact ⟨middle, by simpa only [StateT.run_pure, id_pure_eq]
        using initialRun.catchNull ResponseValue.list⟩
    · simp only
      split
      · exact ⟨middle, by simpa only [StateT.run_pure, id_pure_eq]
          using initialRun.catchNull ResponseValue.list⟩
      · let cutFinish := ((ScheduledExecution.completeListValue schema resolvers variables fuel
          itemType fields (values.take usage.initialCount) path 0 usages context).run left).2
        let eagerFinish := ((Execution.completeListValue schema resolvers variables fuel itemType
          (fields.map (field keys)) (values.take usage.initialCount) path 0 (usages.map keys)
          (context.map (fragment keys))).run right).2
        have afterBoundary : middle (cutFinish + 1) = eagerFinish + 1 := by
          simpa only [Nat.add_zero, initialRun.supplies.boundary]
            using initialRun.supplies.fresh 1
        have suppliesAfter := initialRun.supplies.advance (Nat.le_succ cutFinish)
        rw [afterBoundary] at suppliesAfter
        obtain ⟨next, items⟩ := streamItems_run_of_values schema resolvers variables fuel children
          itemType (fields.map (fun details => { details with deferUsage := none }))
          (values.drop usage.initialCount) path usage.initialCount middle (cutFinish + 1)
          (eagerFinish + 1) suppliesAfter (by
            intro details member
            obtain ⟨original, _, rfl⟩ := List.mem_map.mp member
            simp [UsageBefore])
        have mappedFields :
            (fields.map (fun details => { details with deferUsage := none })).map (field middle)
            = (fields.map (field keys)).map (fun details => { details with deferUsage := none }) := by
          rw [mapped_stream_fields]
          simp [List.map_map, field, Function.comp_def]
        rw [mappedFields] at items
        exact ⟨
          next,
          by
            simpa only [freshNodeRef, run_bind, StateT.run_get, StateT.run_set,
              StateT.run_pure, id_pure_eq]
              using initialRun.withStream items path usage.label
        ⟩

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.ScheduledWork
