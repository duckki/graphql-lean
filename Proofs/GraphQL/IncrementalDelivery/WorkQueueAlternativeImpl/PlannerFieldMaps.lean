import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.SerializedPlanning
import Proofs.GraphQL.IncrementalDelivery.Semantics.CollectedPaths

/-! Ordered field-Map observations: native replacement equals stable append only when
response keys are fresh. Collector key uniqueness derives that fact through the same fold.
The observer specifies insertion order, not a Map representation or complexity bound.
-/

namespace
  GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.PlannerFieldMaps

open GraphQL.IncrementalDelivery.Execution
open IntervalPlanning PreorderPlanning SerializedPlanning PlannerKeyEncoding

-----------------------------------------------------------------------------------------
-- Ordered observations of Map.set and the native partition fold
-----------------------------------------------------------------------------------------

def putField (group : Name × List FieldDetails) : CollectedFieldsMap → CollectedFieldsMap
  | [] => [group]
  | old :: rest => if old.1 == group.1 then group :: rest else old :: putField group rest

def addMapPartition (key : String) (usages : List Nat) (group : Name × List FieldDetails)
    : List Partition → List Partition
  | [] => [⟨key, usages, [group]⟩]
  | partition :: rest =>
      if partition.key == key then
        { partition with fields := putField group partition.fields } :: rest
      else
        partition :: addMapPartition key usages group rest

def mapStep (index : Index) (parent : List Nat) (plan : Plan)
    (group : Name × List FieldDetails)
    : Plan :=
  let usages := filteredUsages index group.2
  if deferUsageSetsEquivalent usages parent then
    { plan with immediate := putField group plan.immediate }
  else
    {
      plan with
        partitions :=
          addMapPartition (stringKey index group.2) usages group plan.partitions
    }

def buildMapPlan (index : Index) (groups : CollectedFieldsMap) (parent : List Nat := [])
    : Plan :=
  groups.foldl (mapStep index parent) {}

/-- Every payload is a subsequence of the already consumed original collector entries. -/
def OrderedFields (groups : CollectedFieldsMap) (plan : Plan) : Prop :=
  plan.immediate.Sublist groups
  ∧ ∀ partition ∈ plan.partitions, partition.fields.Sublist groups

def UniqueFieldMaps (plan : Plan) : Prop :=
  (plan.immediate.map Prod.fst).Nodup
  ∧ ∀ partition ∈ plan.partitions, (partition.fields.map Prod.fst).Nodup

def FieldMapOptimization : Prop :=
  ∀ index groups parent,
    (groups.map Prod.fst).Nodup
    → buildMapPlan index groups parent = SerializedPlanning.buildPlan index groups parent
      ∧ OrderedFields groups (buildMapPlan index groups parent)
      ∧ UniqueFieldMaps (buildMapPlan index groups parent)

def StackMapPlanningOptimization : Prop :=
  ∀ forest : Forest,
    forest.keys.Nodup
    → ∀ groups parent,
        (groups.map Prod.fst).Nodup
        → (∀ group ∈ groups, FieldsFromForest forest group.2)
        → let index := makeIndex (StackPlanning.traverse forest).completed
          let observed := buildMapPlan index groups parent
          observed.project = buildExecutionPlan groups parent
          ∧ Compatible index forest.keys observed.partitions
          ∧ (observed.partitions.map Partition.key).Nodup
          ∧ OrderedFields groups observed
          ∧ UniqueFieldMaps observed

/-- Actual collection supplies key uniqueness; it is not an extra operation premise. -/
def CollectedFieldMapOptimization : Prop :=
  ∀ (ObjectRef : Type) (schema : Schema) (variables : VariableValues) (parentType : Name)
    (source : ResolverValue ObjectRef) selections usage state index parent,
    let groups :=
      ((collectFields schema variables parentType source selections usage).run
        state).1.collectedFieldsMap
    buildMapPlan index groups parent = SerializedPlanning.buildPlan index groups parent
    ∧ OrderedFields groups (buildMapPlan index groups parent)
    ∧ UniqueFieldMaps (buildMapPlan index groups parent)

-----------------------------------------------------------------------------------------
-- Fresh writes append; duplicate writes retain their old insertion position
-----------------------------------------------------------------------------------------

theorem putField_fresh (group : Name × List FieldDetails) (fields : CollectedFieldsMap)
    (fresh : group.1 ∉ fields.map Prod.fst)
    : putField group fields = fields ++ [group] := by
  induction fields with
  | nil => rfl
  | cons old rest ih =>
      simp only [List.map_cons, List.mem_cons, not_or] at fresh
      simp [putField, Ne.symm fresh.1, ih fresh.2]

private theorem addMapPartition_eq (key : String) (usages : List Nat)
    (group : Name × List FieldDetails) (partitions : List Partition)
    (fresh : ∀ partition ∈ partitions, group.1 ∉ partition.fields.map Prod.fst)
    : addMapPartition key usages group partitions
      = addPartition key usages group partitions := by
  induction partitions with
  | nil => rfl
  | cons partition rest ih =>
      have head := putField_fresh group partition.fields (fresh partition (by simp))
      have tail := ih (fun item member => fresh item (List.mem_cons_of_mem _ member))
      simp only [addMapPartition, addPartition]
      split <;> simp [head, tail]

-----------------------------------------------------------------------------------------
-- Ordered payloads are derived through the actual append fold
-----------------------------------------------------------------------------------------

private theorem addPartition_ordered (consumed : CollectedFieldsMap)
    (key : String) (usages : List Nat) (group : Name × List FieldDetails)
    (partitions : List Partition)
    (ordered : ∀ partition ∈ partitions, partition.fields.Sublist consumed)
    : ∀ partition ∈ addPartition key usages group partitions,
        partition.fields.Sublist (consumed ++ [group]) := by
  induction partitions with
  | nil =>
      intro partition member
      simp only [addPartition, List.mem_singleton] at member
      subst partition
      exact List.sublist_append_right consumed [group]
  | cons partition rest ih =>
      have head := ordered partition (by simp)
      have tail := ih (fun item member => ordered item (List.mem_cons_of_mem _ member))
      simp only [addPartition]
      split
      · intro item member
        simp only [List.mem_cons] at member
        rcases member with rfl | member
        · exact head.append (List.Sublist.refl [group])
        · exact (ordered item (List.mem_cons_of_mem _ member)).trans
            (List.sublist_append_left consumed [group])
      · intro item member
        simp only [List.mem_cons] at member
        rcases member with rfl | member
        · exact head.trans (List.sublist_append_left consumed [group])
        · exact tail item member

private theorem ordered_step (consumed : CollectedFieldsMap) (index : Index)
    (parent : List Nat) (plan : Plan) (group : Name × List FieldDetails)
    (ordered : OrderedFields consumed plan)
    : OrderedFields (consumed ++ [group]) (plan.step index parent group) := by
  dsimp only [Plan.step]
  split
  · exact ⟨ordered.1.append (List.Sublist.refl [group]), fun partition member =>
      (ordered.2 partition member).trans (List.sublist_append_left consumed [group])⟩
  · exact ⟨ordered.1.trans (List.sublist_append_left consumed [group]),
      addPartition_ordered consumed _ _ _ _ ordered.2⟩

private theorem ordered_fold (consumed groups : CollectedFieldsMap) (index : Index)
    (parent : List Nat) (plan : Plan) (ordered : OrderedFields consumed plan)
    : OrderedFields (consumed ++ groups)
        (groups.foldl (Plan.step index parent) plan) := by
  induction groups generalizing consumed plan with
  | nil => simpa using ordered
  | cons group rest ih =>
      have next := ih (consumed ++ [group]) _ (ordered_step consumed index parent plan group ordered)
      simpa only [List.append_assoc, List.singleton_append, List.foldl_cons] using next

private theorem mapStep_eq (consumed : CollectedFieldsMap) (index : Index)
    (parent : List Nat) (plan : Plan) (group : Name × List FieldDetails)
    (ordered : OrderedFields consumed plan) (fresh : group.1 ∉ consumed.map Prod.fst)
    : mapStep index parent plan group = plan.step index parent group := by
  have immediateFresh : group.1 ∉ plan.immediate.map Prod.fst :=
    fun member => fresh ((ordered.1.map Prod.fst).subset member)
  have partitionFresh : ∀ partition ∈ plan.partitions, group.1 ∉ partition.fields.map Prod.fst :=
    fun partition member present => fresh ((ordered.2 partition member).map Prod.fst |>.subset present)
  simp only [mapStep, Plan.step]
  split
  · rw [putField_fresh _ _ immediateFresh]
  · rw [addMapPartition_eq _ _ _ _ partitionFresh]

private theorem map_fold_eq (consumed groups : CollectedFieldsMap) (index : Index)
    (parent : List Nat) (plan : Plan) (ordered : OrderedFields consumed plan)
    (unique : ((consumed ++ groups).map Prod.fst).Nodup)
    : groups.foldl (mapStep index parent) plan
      = groups.foldl (Plan.step index parent) plan := by
  induction groups generalizing consumed plan with
  | nil => rfl
  | cons group rest ih =>
      have fresh : group.1 ∉ consumed.map Prod.fst := by
        have separated := (List.nodup_append.mp (by simpa only [List.map_append] using unique)).2.2
        exact fun member => separated group.1 member group.1 (by simp) rfl
      rw [List.foldl_cons, List.foldl_cons, mapStep_eq consumed index parent plan group ordered fresh]
      apply ih (consumed ++ [group]) _
        (ordered_step consumed index parent plan group ordered)
      simpa only [List.append_assoc, List.singleton_append] using unique

theorem FieldMapOptimization_holds : FieldMapOptimization := by
  intro index groups parent unique
  have empty : OrderedFields [] ({} : Plan) := by simp [OrderedFields]
  have equal := map_fold_eq [] groups index parent {} empty (by simpa using unique)
  have ordered : OrderedFields groups (SerializedPlanning.buildPlan index groups parent) :=
    ordered_fold [] groups index parent {} empty
  refine ⟨equal, ?_, ?_⟩
  · simpa only [buildMapPlan, SerializedPlanning.buildPlan, equal] using ordered
  · rw [show buildMapPlan index groups parent = SerializedPlanning.buildPlan index groups parent from equal]
    exact ⟨(ordered.1.map Prod.fst).nodup unique,
      fun partition member => ((ordered.2 partition member).map Prod.fst).nodup unique⟩

theorem StackMapPlanningOptimization_holds : StackMapPlanningOptimization := by
  intro forest unique groups parent responseKeys fromForest
  obtain ⟨equal, ordered, mapsUnique⟩ := FieldMapOptimization_holds
    (makeIndex (StackPlanning.traverse forest).completed) groups parent responseKeys
  obtain ⟨project, compatible, keysUnique⟩ := StackSerializedPlanningOptimization_holds
    forest unique groups parent fromForest
  exact ⟨equal ▸ project, equal ▸ compatible, equal ▸ keysUnique, ordered, mapsUnique⟩

theorem CollectedFieldMapOptimization_holds : CollectedFieldMapOptimization := by
  intro ObjectRef schema variables parentType source selections usage state index parent
  exact FieldMapOptimization_holds _ _ _
    (Semantics.collectFields_unique schema variables parentType source selections usage state)

theorem collectedSubfields_maps {ObjectRef : Type} (schema : Schema)
    (variables : VariableValues) (parentType : Name) (source : ResolverValue ObjectRef)
    (fields : List FieldDetails) (state : Nat) (index : Index) (parent : List Nat)
    : let groups :=
        ((collectSubfields schema variables parentType source fields).run
          state).1.collectedFieldsMap
      buildMapPlan index groups parent = SerializedPlanning.buildPlan index groups parent
      ∧ OrderedFields groups (buildMapPlan index groups parent)
      ∧ UniqueFieldMaps (buildMapPlan index groups parent) :=
  FieldMapOptimization_holds _ _ _
    (Semantics.collectSubfields_unique schema variables parentType source fields state)

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.PlannerFieldMaps
