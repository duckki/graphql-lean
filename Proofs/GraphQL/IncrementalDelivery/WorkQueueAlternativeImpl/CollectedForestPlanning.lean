import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.OrderedForestAssembly
import Proofs.GraphQL.IncrementalDelivery.Semantics.CollectedParentChains
import Proofs.GraphQL.IncrementalDelivery.Semantics.CollectedPaths

/-! Collector-derived planner construction. Path rows observe the immutable parent
objects already referenced by each field usage; they are not additional runtime records.
The executable observer uses only original fields, not a caller-supplied ghost assignment.
-/

namespace
  GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.CollectedForestPlanning

open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Semantics
open Ancestry ParentChains PreorderPlanning OrderedForestAssembly

def pathRows : List Nat → List (Nat × List Nat)
  | [] => []
  | key :: rest => (key, rest) :: pathRows rest

def rows (groups : CollectedFieldsMap) : List (Nat × List Nat) :=
  groups.flatMap
    (fun group =>
      (group.2.filterMap FieldDetails.deferUsage).flatMap
        (fun usage => pathRows (usage.ref :: usage.ancestors)))

def contexts (groups : CollectedFieldsMap) : Contexts :=
  fun key => (((rows groups).find? (fun pair => pair.1 == key)).map Prod.snd).getD []

def domain (groups : CollectedFieldsMap) : List Nat :=
  ((rows groups).map Prod.fst).eraseDups

def forest (groups : CollectedFieldsMap) : Forest :=
  fieldForest (contexts groups) (domain groups) groups

/-- Whole optimized planner observer: original seeds, early-stop discovery, ordered
assembly, node stack, stable interval filtering, serialized keys and ordered Map writes.
Raw inconsistent usage metadata is outside its generated execution domain.
-/
def buildPlan (groups : CollectedFieldsMap) (parent : List Nat) : ExecutionPlan :=
  (PlannerFieldMaps.buildMapPlan
    (makeIndex (PlannerNodeStack.traverse (forest groups)).completed) groups
    parent).project

def GeneratedPlanning : Prop :=
  ∀ parents state context groups parent,
    Chains parents state
    → GroupsSatisfy (fun field => OptionalUsageAt parents state context field.deferUsage)
        groups
    → (groups.map Prod.fst).Nodup
    → (forest groups).keys.Nodup
      ∧ (∀ group ∈ groups, FieldsFromForest (forest groups) group.2)
      ∧ buildPlan groups parent = buildExecutionPlan groups parent

def RootCollectedPlanning : Prop :=
  ∀ (ObjectRef : Type) (schema : Schema) variables parentType
    (source : ResolverValue ObjectRef) selections state parent,
    let groups :=
      ((collectFields schema variables parentType source selections none).run
        state).1.collectedFieldsMap
    (forest groups).keys.Nodup
    ∧ (∀ group ∈ groups, FieldsFromForest (forest groups) group.2)
    ∧ buildPlan groups parent = buildExecutionPlan groups parent

-----------------------------------------------------------------------------------------
-- Parent-object observations are all suffixes of the original immutable usage paths
-----------------------------------------------------------------------------------------

theorem pathRows_mem (keys : List Nat) (pair : Nat × List Nat)
    : pair ∈ pathRows keys ↔ ∃ front, keys = front ++ pair.1 :: pair.2 := by
  induction keys with
  | nil => simp [pathRows]
  | cons key rest ih =>
      constructor
      · intro member
        rcases List.mem_cons.mp member with rfl | member
        · exact ⟨[], rfl⟩
        · obtain ⟨front, equal⟩ := ih.1 member
          exact ⟨key :: front, by simp [equal]⟩
      · rintro ⟨front, equal⟩
        cases front with
        | nil =>
            cases pair
            simp only [List.nil_append, List.cons.injEq] at equal
            obtain ⟨rfl, rfl⟩ := equal
            simp [pathRows]
        | cons first tail =>
            simp only [List.cons_append, List.cons.injEq] at equal
            exact List.mem_cons_of_mem _ (ih.2 ⟨tail, equal.2⟩)

theorem pathRows_closed (keys : List Nat) (pair : Nat × List Nat)
    (member : pair ∈ pathRows keys) (front : List Nat) (ancestor : Nat)
    (suffix : List Nat) (chain : pair.2 = front ++ ancestor :: suffix)
    : (ancestor, suffix) ∈ pathRows keys := by
  obtain ⟨before, equal⟩ := (pathRows_mem keys pair).1 member
  apply (pathRows_mem keys (ancestor, suffix)).2
  exact ⟨before ++ pair.1 :: front, by simp [equal, chain, List.append_assoc]⟩

theorem rows_closed (groups : CollectedFieldsMap) (pair : Nat × List Nat)
    (member : pair ∈ rows groups) (front : List Nat) (ancestor : Nat) (suffix : List Nat)
    (chain : pair.2 = front ++ ancestor :: suffix)
    : (ancestor, suffix) ∈ rows groups := by
  obtain ⟨group, groupMember, selected⟩ := List.mem_flatMap.mp member
  obtain ⟨usage, usageMember, present⟩ := List.mem_flatMap.mp selected
  exact List.mem_flatMap.mpr ⟨group, groupMember,
    List.mem_flatMap.mpr ⟨usage, usageMember, pathRows_closed _ pair present front ancestor suffix chain⟩⟩

theorem rows_known (parents : Assignment) (state : Nat) (context : DeferMap)
    (groups : CollectedFieldsMap) (chains : Chains parents state)
    (known
      : GroupsSatisfy
          (fun field => OptionalUsageAt parents state context field.deferUsage) groups)
    : ∀ pair ∈ rows groups, pair.1 < state ∧ parents pair.1 = pair.2 := by
  intro pair member
  obtain ⟨group, groupMember, selected⟩ := List.mem_flatMap.mp member
  obtain ⟨usage, usageMember, present⟩ := List.mem_flatMap.mp selected
  obtain ⟨field, fieldMember, found⟩ := List.mem_filterMap.mp usageMember
  have usageKnown := known group groupMember field fieldMember usage found
  obtain ⟨front, equal⟩ := (pathRows_mem _ pair).1 present
  cases front with
  | nil =>
      simp only [List.nil_append, List.cons.injEq] at equal
      exact ⟨equal.1 ▸ usageKnown.1, equal.1 ▸ usageKnown.2.1.trans equal.2⟩
  | cons first tail =>
      simp only [List.cons_append, List.cons.injEq] at equal
      exact chains usage.ref usageKnown.1 tail pair.1 pair.2 (usageKnown.2.1.trans equal.2)

theorem contexts_known (parents : Assignment) (state : Nat) (groups : CollectedFieldsMap)
    (known : ∀ pair ∈ rows groups, pair.1 < state ∧ parents pair.1 = pair.2)
    (key : Nat) (member : key ∈ domain groups)
    : key < state ∧ contexts groups key = parents key := by
  have present : key ∈ (rows groups).map Prod.fst := by simpa [domain] using member
  obtain ⟨pair, pairMember, equal⟩ := List.mem_map.mp present
  have witness : ∃ row ∈ rows groups, (row.1 == key) = true := ⟨pair, pairMember, by simp [equal]⟩
  cases found : (rows groups).find? (fun pair => pair.1 == key) with
  | none =>
      have someRow := List.find?_isSome.mpr witness
      simp [found] at someRow
  | some row =>
      have rowMember := List.mem_of_find?_eq_some found
      have keyEq : row.1 = key := by simpa using List.find?_some found
      have rowKnown := known row rowMember
      refine ⟨keyEq ▸ rowKnown.1, ?_⟩
      simp only [contexts, found, Option.map_some, Option.getD_some]
      exact keyEq ▸ rowKnown.2.symm

theorem rows_contexts_closed (parents : Assignment) (state : Nat)
    (groups : CollectedFieldsMap)
    (known : ∀ pair ∈ rows groups, pair.1 < state ∧ parents pair.1 = pair.2)
    : ClosedContexts (contexts groups) (domain groups) := by
  intro key member front ancestor suffix chain
  have present : key ∈ (rows groups).map Prod.fst := by simpa [domain] using member
  obtain ⟨pair, pairMember, equal⟩ := List.mem_map.mp present
  have exactContext : contexts groups key = pair.2 :=
    (contexts_known parents state groups known key member).2.trans (equal ▸ (known pair pairMember).2)
  have ancestorMember := rows_closed groups pair pairMember front ancestor suffix (exactContext ▸ chain)
  have ancestorDomain : ancestor ∈ domain groups := by
    simp only [domain, List.mem_eraseDups]
    exact List.mem_map.mpr ⟨(ancestor, suffix), ancestorMember, rfl⟩
  exact ⟨
    ancestorDomain,
    (contexts_known parents state groups known ancestor ancestorDomain).2.trans
      (known _ ancestorMember).2
  ⟩

theorem fields_in_contexts (parents : Assignment) (state : Nat) (context : DeferMap)
    (groups : CollectedFieldsMap) (chains : Chains parents state)
    (known
      : GroupsSatisfy
          (fun field => OptionalUsageAt parents state context field.deferUsage) groups)
    : FieldsInContexts (contexts groups) (domain groups) groups := by
  intro group member usage present
  obtain ⟨field, fieldMember, found⟩ := List.mem_filterMap.mp present
  have usageKnown := known group member field fieldMember usage found
  have usageRow : (usage.ref, usage.ancestors) ∈ rows groups :=
    List.mem_flatMap.mpr ⟨group, member, List.mem_flatMap.mpr
      ⟨usage, present, by simp [pathRows]⟩⟩
  have usageDomain : usage.ref ∈ domain groups := by
    simp only [domain, List.mem_eraseDups]
    exact List.mem_map.mpr ⟨_, usageRow, rfl⟩
  exact ⟨
    usageDomain,
    usageKnown.2.1.symm.trans
      (contexts_known parents state groups
        (rows_known parents state context groups chains known) _ usageDomain).2.symm
  ⟩

theorem GeneratedPlanning_holds : GeneratedPlanning := by
  intro parents state context groups parent chains known unique
  have closed := rows_contexts_closed parents state groups (rows_known parents state context groups chains known)
  have fields := fields_in_contexts parents state context groups chains known
  obtain ⟨forestUnique, fromForest, exactPlan, _⟩ :=
    OrderedFieldPlanningOptimization_holds _ _ groups parent closed fields unique
  exact ⟨forestUnique, fromForest, exactPlan⟩

theorem RootCollectedPlanning_holds : RootCollectedPlanning := by
  intro ObjectRef schema variables parentType source selections state parent
  obtain ⟨_, next, _, _, chains, _, known⟩ := collectFields_chains schema variables parentType source
    selections none (fun _ => []) state [] [] (by simp [Valid]) (by simp [Chains])
      (by simp [MapAt]) (by simp [OptionalUsageAt])
  exact GeneratedPlanning_holds next _ _ _ parent chains known
    (collectFields_unique schema variables parentType source selections none state)

theorem subfields_planning (schema : Schema) (variables : VariableValues)
    (parentType : Name) (source : ResolverValue ObjectRef) (fields : List FieldDetails)
    (parents : Assignment) (state : Nat) (context : DeferMap) (path : ResponsePath)
    (parent : List Nat) (valid : Valid parents state) (chains : Chains parents state)
    (metadata : MapAt parents state context)
    (known : ∀ field ∈ fields, OptionalUsageAt parents state context field.deferUsage)
    : let groups :=
        ((collectSubfields schema variables parentType source fields).run
          state).1.collectedFieldsMap
      (forest groups).keys.Nodup
      ∧ (∀ group ∈ groups, FieldsFromForest (forest groups) group.2)
      ∧ buildPlan groups parent = buildExecutionPlan groups parent := by
  obtain ⟨_, next, _, _, finalChains, _, finalKnown⟩ := collectSubfields_chains schema variables
    parentType source fields parents state context path valid chains metadata known
  exact GeneratedPlanning_holds next _ _ _ parent finalChains finalKnown
    (collectSubfields_unique schema variables parentType source fields state)

end
  GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.CollectedForestPlanning
