import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.ForestParentSource
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.PlannerNodeStack

/-! Ordered parent-table assembly. Context lists are ghost observations of immutable
parent links, not runtime ranks or another native index. Filtering the insertion-order
domain observes the native roots/children arrays; implementations build those arrays in
one pass. The depth bound only makes this structural observer total.
-/

namespace
  GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.OrderedForestAssembly

open GraphQL.IncrementalDelivery.Execution
open PreorderPlanning

abbrev Contexts := Nat → List Nat

/-- Every suffix is the exact context of that ancestor, which is in the same domain.
This is stronger than transitive membership alone; malformed ordered chains are excluded.
-/
def ClosedContexts (ancestors : Contexts) (nodes : List Nat) : Prop :=
  ∀ key ∈ nodes,
    ∀ front ancestor suffix,
      ancestors key = front ++ ancestor :: suffix
      → ancestor ∈ nodes ∧ ancestors ancestor = suffix

def rootsAt (ancestors : Contexts) (nodes context : List Nat) : List Nat :=
  nodes.filter (fun key => ancestors key == context)

def assembleAt (ancestors : Contexts) (nodes : List Nat)
    : Nat → List Nat → List Nat → Forest
  | 0, _, _ => .empty
  | fuel + 1, context, roots =>
      roots.foldr
        (fun key rest =>
          .node key
            (assembleAt ancestors nodes fuel (key :: context)
              (rootsAt ancestors nodes (key :: context))) rest) .empty

def depth (ancestors : Contexts) (nodes : List Nat) : Nat :=
  nodes.foldr (fun key bound => max (ancestors key).length bound) 0 + 1

def assemble (ancestors : Contexts) (nodes : List Nat) : Forest :=
  assembleAt ancestors nodes (depth ancestors nodes) [] (rootsAt ancestors nodes [])

def forestRoots : Forest → List Nat
  | .empty => []
  | .node key _ rest => key :: forestRoots rest

def childLists : Forest → List (Nat × List Nat)
  | .empty => []
  | .node key children rest =>
      (key, forestRoots children) :: (childLists children ++ childLists rest)

def OrderedForestConstruction : Prop :=
  ∀ ancestors nodes,
    nodes.Nodup
    → ClosedContexts ancestors nodes
    → let forest := assemble ancestors nodes
      forest.keys.Nodup
      ∧ (∀ key, key ∈ forest.keys ↔ key ∈ nodes)
      ∧ (∀ entry ∈ forest.encode 0 [], entry.usage.ancestors = ancestors entry.usage.ref)
      ∧ forestRoots forest = nodes.filter (fun key => (ancestors key).head? == none)
      ∧ (∀ key ∈ nodes,
          rootsAt ancestors nodes (key :: ancestors key)
          = nodes.filter (fun child => (ancestors child).head? == some key))
      ∧ (∀ pair ∈ childLists forest,
          pair.2 = nodes.filter (fun child => (ancestors child).head? == some pair.1))

-----------------------------------------------------------------------------------------
-- Assembly soundness and disjoint branches, before any planner consequence
-----------------------------------------------------------------------------------------

private theorem rootsAt_mem (ancestors : Contexts) (nodes context : List Nat) (key : Nat)
    : key ∈ rootsAt ancestors nodes context ↔ key ∈ nodes ∧ ancestors key = context := by
  simp [rootsAt]

private theorem suffix_equal {left right whole : List Nat}
    (hl : left <:+ whole) (hr : right <:+ whole) (lengths : left.length = right.length)
    : left = right := by
  rw [List.suffix_iff_eq_drop] at hl hr
  rw [hl, hr, lengths]

private theorem assembly_sound (ancestors : Contexts) (nodes : List Nat) (fuel : Nat)
    (context roots : List Nat)
    (valid : ∀ key ∈ roots, key ∈ nodes ∧ ancestors key = context)
    : (∀ base entry,
        entry ∈ (assembleAt ancestors nodes fuel context roots).encode base context
        → entry.usage.ref ∈ nodes ∧ entry.usage.ancestors = ancestors entry.usage.ref)
      ∧ (∀ key ∈ (assembleAt ancestors nodes fuel context roots).keys,
          ∃ root ∈ roots, root :: context <:+ key :: ancestors key) := by
  induction fuel generalizing context roots with
  | zero => simp [assembleAt, Forest.encode, Forest.keys]
  | succ fuel ih =>
      induction roots with
      | nil => simp [assembleAt, Forest.encode, Forest.keys]
      | cons root rest restIH =>
          obtain ⟨rootMember, rootContext⟩ := valid root (by simp)
          have child := ih (root :: context) (rootsAt ancestors nodes (root :: context))
            (fun key member => (rootsAt_mem _ _ _ _).1 member)
          have sibling := restIH (fun key member => valid key (by simp [member]))
          constructor
          · intro base entry present
            simp only [assembleAt, List.foldr_cons, Forest.encode, List.mem_cons,
              List.mem_append] at present
            rcases present with rfl | present | present
            · exact ⟨rootMember, rootContext.symm⟩
            · exact child.1 _ _ present
            · exact sibling.1 _ _ present
          · intro key present
            simp only [assembleAt, List.foldr_cons, Forest.keys, List.mem_cons,
              List.mem_append] at present
            rcases present with rfl | present | present
            · exact ⟨key, by simp, by simp [rootContext]⟩
            · obtain ⟨childRoot, _, suffix⟩ := child.2 key present
              exact ⟨root, by simp, (List.suffix_cons childRoot (root :: context)).trans suffix⟩
            · obtain ⟨other, member, suffix⟩ := sibling.2 key present
              exact ⟨other, by simp [member], suffix⟩

private theorem assembly_unique (ancestors : Contexts) (nodes : List Nat)
    (unique : nodes.Nodup) (fuel : Nat) (context roots : List Nat)
    (rootsUnique : roots.Nodup)
    (valid : ∀ key ∈ roots, key ∈ nodes ∧ ancestors key = context)
    : (assembleAt ancestors nodes fuel context roots).keys.Nodup := by
  induction fuel generalizing context roots with
  | zero => simp [assembleAt, Forest.keys]
  | succ fuel ih =>
      induction roots with
      | nil => simp [assembleAt, Forest.keys]
      | cons root rest restIH =>
          obtain ⟨absent, restUnique⟩ := List.nodup_cons.mp rootsUnique
          have rootContext := (valid root (by simp)).2
          have childValid := fun key member => (rootsAt_mem ancestors nodes (root :: context) key).1 member
          have childSound := (assembly_sound ancestors nodes fuel (root :: context)
            (rootsAt ancestors nodes (root :: context)) childValid).2
          have restValid := fun key member => valid key (List.mem_cons_of_mem root member)
          have restSound := (assembly_sound ancestors nodes (fuel + 1) context rest restValid).2
          simp only [assembleAt, List.foldr_cons, Forest.keys, List.nodup_cons,
            List.nodup_append, List.mem_append]
          refine ⟨?_, ih _ _ (unique.filter _) childValid,
            restIH restUnique restValid, ?_⟩
          · intro member
            rcases member with childMember | restMember
            · obtain ⟨childRoot, _, suffix⟩ := childSound root childMember
              have bound := suffix.length_le
              simp only [List.length_cons, rootContext] at bound
              omega
            · obtain ⟨other, present, suffix⟩ := restSound root restMember
              have same := suffix.eq_of_length (by simp [rootContext])
              have equal : other = root := (List.cons.inj same).1
              exact absent (equal ▸ present)
          · intro key childMember other restMember equal
            subst other
            obtain ⟨childRoot, _, childSuffix⟩ := childSound key childMember
            obtain ⟨other, present, otherSuffix⟩ := restSound key restMember
            have rootSuffix := (List.suffix_cons childRoot (root :: context)).trans childSuffix
            have same := suffix_equal rootSuffix otherSuffix (by simp)
            exact absent ((List.cons.inj same).1 ▸ present)

-----------------------------------------------------------------------------------------
-- Closed parent chains ensure that depth truncation never loses a node
-----------------------------------------------------------------------------------------

private theorem assembly_covers (ancestors : Contexts) (nodes : List Nat)
    (closed : ClosedContexts ancestors nodes) (fuel : Nat) (context : List Nat)
    (key : Nat) (member : key ∈ nodes) (suffix : context <:+ ancestors key)
    (bound : (ancestors key).length < fuel + context.length)
    : key
      ∈ (assembleAt ancestors nodes fuel context
          (rootsAt ancestors nodes context)).keys := by
  induction fuel generalizing context with
  | zero => have h := suffix.length_le; omega
  | succ fuel ih =>
      obtain ⟨front, equal⟩ := List.suffix_iff_exists_eq_append.mp suffix
      cases reversed : front.reverse with
      | nil =>
          have empty : front = [] := List.reverse_eq_nil_iff.mp reversed
          have selected : key ∈ rootsAt ancestors nodes context :=
            (rootsAt_mem _ _ _ _).2 ⟨member, by simpa [empty] using equal⟩
          generalize rootsAt ancestors nodes context = roots at selected ⊢
          induction roots with
          | nil => simp at selected
          | cons root rest restIH =>
              simp only [assembleAt, List.foldr_cons, Forest.keys, List.mem_cons,
                List.mem_append]
              rcases List.mem_cons.mp selected with rfl | present
              · exact Or.inl rfl
              · exact Or.inr (Or.inr (restIH present))
      | cons root reversedRest =>
          have split : front = reversedRest.reverse ++ [root] := by
            rw [← List.reverse_reverse front, reversed, List.reverse_cons]
          have chain : ancestors key = reversedRest.reverse ++ root :: context := by
            simpa [split, List.append_assoc] using equal
          obtain ⟨rootMember, rootContext⟩ := closed key member reversedRest.reverse root context chain
          have selected := (rootsAt_mem ancestors nodes context root).2 ⟨rootMember, rootContext⟩
          have below := ih (root :: context)
            (List.suffix_iff_exists_eq_append.mpr ⟨reversedRest.reverse, chain⟩)
            (by simp only [List.length_cons]; omega)
          generalize rootsAt ancestors nodes context = roots at selected ⊢
          induction roots with
          | nil => simp at selected
          | cons other rest restIH =>
              simp only [assembleAt, List.foldr_cons, Forest.keys, List.mem_cons, List.mem_append]
              rcases List.mem_cons.mp selected with rfl | present
              · exact Or.inr (Or.inl below)
              · exact Or.inr (Or.inr (restIH present))

private theorem depth_bounds (ancestors : Contexts) (nodes : List Nat)
    : ∀ key ∈ nodes, (ancestors key).length < depth ancestors nodes := by
  have bounds : ∀ key ∈ nodes,
      (ancestors key).length ≤ nodes.foldr (fun key bound => max (ancestors key).length bound) 0 := by
    induction nodes with
    | nil => simp
    | cons root rest ih =>
        intro key present
        rcases List.mem_cons.mp present with rfl | present
        · exact Nat.le_max_left _ _
        · exact Nat.le_trans (ih key present) (Nat.le_max_right _ _)
  intro key member
  have bound := bounds key member
  unfold depth
  omega

private theorem assembly_roots (ancestors : Contexts) (nodes : List Nat) (fuel : Nat)
    (context roots : List Nat)
    : forestRoots (assembleAt ancestors nodes (fuel + 1) context roots) = roots := by
  induction roots with
  | nil => rfl
  | cons key rest ih =>
      change key :: forestRoots (assembleAt ancestors nodes (fuel + 1) context rest) = key :: rest
      rw [ih]

private theorem bounded_roots (ancestors : Contexts) (nodes : List Nat) (fuel : Nat)
    (context : List Nat)
    (bound : ∀ key ∈ nodes, (ancestors key).length < fuel + context.length)
    : forestRoots
        (assembleAt ancestors nodes fuel context (rootsAt ancestors nodes context))
      = rootsAt ancestors nodes context := by
  cases fuel with
  | zero =>
      have empty : rootsAt ancestors nodes context = [] := by
        apply List.eq_nil_iff_forall_not_mem.mpr
        intro key member
        obtain ⟨present, equal⟩ := (rootsAt_mem _ _ _ _).1 member
        have h := bound key present
        simp only [equal, Nat.zero_add] at h
        omega
      simp [assembleAt, forestRoots, empty]
  | succ fuel => exact assembly_roots _ _ _ _ _

private theorem assembly_children (ancestors : Contexts) (nodes : List Nat) (fuel : Nat)
    (context roots : List Nat)
    (valid : ∀ key ∈ roots, key ∈ nodes ∧ ancestors key = context)
    (bound : ∀ key ∈ nodes, (ancestors key).length < fuel + context.length)
    : ∀ pair ∈ childLists (assembleAt ancestors nodes fuel context roots),
        pair.1 ∈ nodes
        ∧ pair.2 = rootsAt ancestors nodes (pair.1 :: ancestors pair.1) := by
  induction fuel generalizing context roots with
  | zero => simp [assembleAt, childLists]
  | succ fuel ih =>
      induction roots with
      | nil => simp [assembleAt, childLists]
      | cons key rest restIH =>
          intro pair member
          simp only [assembleAt, List.foldr_cons, childLists, List.mem_cons, List.mem_append] at member
          have childBound : ∀ key ∈ nodes, (ancestors key).length < fuel + (key :: context).length := by
            intro item present
            have h := bound item present
            simp only [List.length_cons]
            omega
          rcases member with rfl | child | sibling
          · obtain ⟨present, equal⟩ := valid key (by simp)
            exact ⟨present, by simpa [equal] using bounded_roots ancestors nodes fuel (key :: context) childBound⟩
          · exact ih _ _ (fun item present => (rootsAt_mem _ _ _ _).1 present) childBound pair child
          · exact restIH (fun item present => valid item (by simp [present])) pair sibling

theorem OrderedForestConstruction_holds : OrderedForestConstruction := by
  intro ancestors nodes unique closed
  have valid := fun key member => (rootsAt_mem ancestors nodes [] key).1 member
  have sound := assembly_sound ancestors nodes (depth ancestors nodes) [] (rootsAt ancestors nodes []) valid
  refine ⟨assembly_unique ancestors nodes unique _ _ _ (unique.filter _) valid, ?_,
    fun entry present => (sound.1 0 entry present).2, ?_, ?_, ?_⟩
  · intro key
    constructor
    · intro present
      rw [← Forest.encode_keys (assemble ancestors nodes) 0 []] at present
      obtain ⟨entry, entryMember, equal⟩ := List.mem_map.mp present
      exact equal ▸ (sound.1 0 entry entryMember).1
    · intro present
      exact assembly_covers ancestors nodes closed _ [] key present
        (by simp) (by simpa using depth_bounds ancestors nodes key present)
  · simp only [assemble, depth, assembly_roots, rootsAt]
    apply List.filter_congr
    intro key _
    cases ancestors key <;> rfl
  · have edges : ∀ key ∈ nodes,
        rootsAt ancestors nodes (key :: ancestors key)
          = nodes.filter (fun child => (ancestors child).head? == some key) := by
      intro key member
      apply List.filter_congr
      intro child childMember
      apply Bool.eq_iff_iff.mpr
      simp only [beq_iff_eq]
      constructor
      · intro equal; simp [equal]
      · intro head
        cases eq : ancestors child with
        | nil => simp [eq] at head
        | cons ancestor suffix =>
            have equal : ancestor = key := by simpa [eq] using head
            subst ancestor
            have context := (closed child childMember [] key suffix (by simpa using eq)).2
            simp [context]
    exact edges
  · intro pair member
    obtain ⟨present, equal⟩ := assembly_children ancestors nodes _ [] _ valid
      (by simpa using depth_bounds ancestors nodes) pair member
    rw [equal]
    apply List.filter_congr
    intro child childMember
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq]
    constructor
    · intro equal; simp [equal]
    · intro head
      cases eq : ancestors child with
      | nil => simp [eq] at head
      | cons ancestor suffix =>
          have equal : ancestor = pair.1 := by simpa [eq] using head
          subst ancestor
          have context := (closed child childMember [] pair.1 suffix (by simpa using eq)).2
          simp [context]

-----------------------------------------------------------------------------------------
-- One run: original field seeds, parent discovery, ordered assembly, stack and planner
-----------------------------------------------------------------------------------------

def parentTable (ancestors : Contexts) (domain : List Nat) : ParentDiscovery.Parents :=
  fun key => if key ∈ domain then (ancestors key).head? else none

def discovered (ancestors : Contexts) (domain : List Nat) (groups : CollectedFieldsMap)
    : ParentDiscovery.Result :=
  ParentDiscovery.discover (parentTable ancestors domain)
    (fun key => (ancestors key).length) (ForestParentSource.fieldSeeds groups)

def fieldForest (ancestors : Contexts) (domain : List Nat) (groups : CollectedFieldsMap)
    : Forest :=
  assemble ancestors (discovered ancestors domain groups).nodes

def FieldsInContexts (ancestors : Contexts) (domain : List Nat)
    (groups : CollectedFieldsMap)
    : Prop :=
  ∀ group ∈ groups,
  ∀ usage ∈ group.2.filterMap FieldDetails.deferUsage,
    usage.ref ∈ domain ∧ usage.ancestors = ancestors usage.ref

def OrderedFieldPlanningOptimization : Prop :=
  ∀ ancestors domain groups parent,
    ClosedContexts ancestors domain
    → FieldsInContexts ancestors domain groups
    → (groups.map Prod.fst).Nodup
    → let forest := fieldForest ancestors domain groups
      let observed :=
        PlannerFieldMaps.buildMapPlan
          (makeIndex (PlannerNodeStack.traverse forest).completed) groups parent
      forest.keys.Nodup
      ∧ (∀ group ∈ groups, FieldsFromForest forest group.2)
      ∧ observed.project = buildExecutionPlan groups parent
      ∧ SerializedPlanning.Compatible
          (makeIndex (PlannerNodeStack.traverse forest).completed) forest.keys
          observed.partitions
      ∧ (observed.partitions.map SerializedPlanning.Partition.key).Nodup
      ∧ PlannerFieldMaps.OrderedFields groups observed
      ∧ PlannerFieldMaps.UniqueFieldMaps observed

theorem parentTable_decreasing (ancestors : Contexts) (domain : List Nat)
    (closed : ClosedContexts ancestors domain)
    : ParentDiscovery.Decreasing (parentTable ancestors domain)
        (fun key => (ancestors key).length) := by
  intro key ancestor edge
  unfold parentTable at edge
  split at edge
  next member =>
    cases eq : ancestors key with
    | nil => simp [eq] at edge
    | cons first rest =>
        have equal : first = ancestor := by simpa [eq] using edge
        subst first
        have context := (closed key member [] ancestor rest (by simpa using eq)).2
        simp [eq, context]
  next => contradiction

theorem closedContexts_restrict (ancestors : Contexts) (domain nodes : List Nat)
    (closed : ClosedContexts ancestors domain) (subset : nodes.Subset domain)
    (parentClosed : ParentDiscovery.ParentClosed (parentTable ancestors domain) nodes)
    : ClosedContexts ancestors nodes := by
  intro key member front
  induction front generalizing key with
  | nil =>
      intro ancestor suffix chain
      have context := closed key (subset member) [] ancestor suffix chain
      refine ⟨parentClosed key member ancestor ?_, context.2⟩
      simp [parentTable, subset member, chain]
  | cons first rest ih =>
      intro ancestor suffix chain
      have firstContext := closed key (subset member) [] first (rest ++ ancestor :: suffix) chain
      have firstMember := parentClosed key member first (by simp [parentTable, subset member, chain])
      exact ih first firstMember ancestor suffix firstContext.2

theorem discovered_contexts (ancestors : Contexts) (domain : List Nat)
    (groups : CollectedFieldsMap) (closed : ClosedContexts ancestors domain)
    (fields : FieldsInContexts ancestors domain groups)
    : (discovered ancestors domain groups).nodes.Nodup
      ∧ ClosedContexts ancestors (discovered ancestors domain groups).nodes
      ∧ FieldsInContexts ancestors (discovered ancestors domain groups).nodes groups := by
  have decreasing := parentTable_decreasing ancestors domain closed
  obtain ⟨_, unique, parentClosed, reachable, _, _⟩ := ParentDiscovery.ParentDiscoveryOptimization_holds
    (parentTable ancestors domain) (fun key => (ancestors key).length) decreasing (ForestParentSource.fieldSeeds groups)
  have seeds : (ForestParentSource.fieldSeeds groups).Subset domain := by
    intro key member
    obtain ⟨group, groupMember, selected⟩ := List.mem_flatMap.mp member
    obtain ⟨usage, usageMember, equal⟩ := List.mem_map.mp selected
    exact equal ▸ (fields group groupMember usage usageMember).1
  have subset : (discovered ancestors domain groups).nodes.Subset domain := by
    intro key member
    have reached := (reachable key).1 member
    clear member
    induction reached with
    | seed node present => exact seeds present
    | ancestor node ancestor _ edge covered =>
        have head : (ancestors node).head? = some ancestor := by simpa [parentTable, covered] using edge
        cases eq : ancestors node with
        | nil => simp [eq] at head
        | cons first rest =>
            have equal : first = ancestor := by simpa [eq] using head
            exact equal ▸ (closed node covered [] first rest (by simpa using eq)).1
  refine ⟨
    unique,
    closedContexts_restrict ancestors domain _ closed subset parentClosed,
    ?_
  ⟩
  intro group groupMember usage usageMember
  refine ⟨
    (reachable usage.ref).2 (.seed _ ?_),
    (fields group groupMember usage usageMember).2
  ⟩
  exact List.mem_flatMap.mpr
    ⟨group, groupMember, List.mem_map.mpr ⟨usage, usageMember, rfl⟩⟩

theorem assembled_fields (ancestors : Contexts) (nodes : List Nat)
    (groups : CollectedFieldsMap) (unique : nodes.Nodup)
    (closed : ClosedContexts ancestors nodes)
    (fields : FieldsInContexts ancestors nodes groups)
    : (assemble ancestors nodes).keys.Nodup
      ∧ ∀ group ∈ groups, FieldsFromForest (assemble ancestors nodes) group.2 := by
  obtain ⟨forestUnique, domain, contexts, _, _, _⟩ := OrderedForestConstruction_holds ancestors nodes unique closed
  refine ⟨forestUnique, ?_⟩
  intro group groupMember usage usageMember
  have member := (domain usage.ref).2 (fields group groupMember usage usageMember).1
  rw [← Forest.encode_keys (assemble ancestors nodes) 0 []] at member
  obtain ⟨entry, entryMember, equal⟩ := List.mem_map.mp member
  exact ⟨entry, entryMember, equal,
    (contexts entry entryMember).trans (equal ▸ (fields group groupMember usage usageMember).2.symm)⟩

theorem OrderedFieldPlanningOptimization_holds : OrderedFieldPlanningOptimization := by
  intro ancestors domain groups parent closed fields names
  obtain ⟨unique, discoveredClosed, discoveredFields⟩ := discovered_contexts ancestors domain groups closed fields
  obtain ⟨forestUnique, fromForest⟩ := assembled_fields ancestors _ groups unique discoveredClosed discoveredFields
  exact ⟨forestUnique, fromForest,
    PlannerNodeStack.NodeStackMapPlanningOptimization_holds _ forestUnique groups parent names fromForest⟩

end
  GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.OrderedForestAssembly
