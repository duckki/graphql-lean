import Proofs.GraphQL.IncrementalDelivery.WorkQueueSemantics.StructuralEquivalence

/-! Proof-only delivery-key correspondence for recursively retained Work. Addresses and
stream indices are structural occurrences, not allocation keys, and are never renamed.
The same map is used for nodes, ancestors, owners and nested work. This does not construct
the map from cancelled execution or permit changing fixed payloads/error counts.
-/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.KeyRenaming

open GraphQL.IncrementalDelivery.Execution
open WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- One key map throughout the original Work representation
-----------------------------------------------------------------------------------------

def node (keys : Nat → Nat) (original : DeliveryNode) : DeliveryNode :=
  { original with ref := keys original.ref }

def fragment (keys : Nat → Nat) (original : DeferredFragment) : DeferredFragment :=
  { node := node keys original.node, ancestors := original.ancestors.map (node keys) }

def work (keys : Nat → Nat) : Work → Work
  | .empty => .empty
  | .declareGroups groups tasks =>
      .declareGroups (groups.map (fragment keys)) (work keys tasks)
  | .combine left right => .combine (work keys left) (work keys right)
  | .executionGroup groups path result children =>
      .executionGroup (groups.map (fragment keys)) path result (work keys children)
  | .stream original items =>
      .stream (node keys original) (items.map (fun item => (item.1, work keys item.2)))
termination_by original => sizeOf original
decreasing_by
  all_goals simp_wf
  all_goals try decreasing_trivial
  have smaller := List.sizeOf_lt_of_mem ‹item ∈ items›
  rcases item with ⟨result, children⟩
  simp only [Prod.mk.sizeOf_spec] at smaller
  dsimp only
  omega

def payload (keys : Nat → Nat) : Payload → Payload
  | .object path result => .object path result
  | .item original result => .item (node keys original) result

def location (keys : Nat → Nat) (original : WorkLocation) : WorkLocation :=
  ⟨work keys original.current, original.producer, original.owners.map keys⟩

theorem group_keys (keys : Nat → Nat) (groups : List DeferredFragment)
    : (groups.map (fragment keys)).map (fun group => group.node.ref)
      = (groups.map (fun group => group.node.ref)).map keys := by
  simp only [List.map_map]
  rfl

theorem ancestor_keys (keys : Nat → Nat) (original : DeferredFragment)
    : (fragment keys original).ancestors.map DeliveryNode.ref
      = (original.ancestors.map DeliveryNode.ref).map keys := by
  simp only [fragment, List.map_map]
  rfl

theorem payload_failure (keys : Nat → Nat) (original : Payload)
    : (payload keys original).failure = original.failure := by
  cases original with
  | object => rfl
  | item descriptor result => cases result <;> rfl

theorem node_comp (outer inner : Nat → Nat) (original : DeliveryNode)
    : node outer (node inner original) = node (outer ∘ inner) original :=
  rfl

theorem fragment_comp (outer inner : Nat → Nat) (original : DeferredFragment)
    : fragment outer (fragment inner original) = fragment (outer ∘ inner) original := by
  simp only [fragment, List.map_map]
  rfl

/-- Extending one map through successive cuts is the same as composing Work renamings. -/
theorem work_comp (outer inner : Nat → Nat) (original : Work)
    : work outer (work inner original) = work (outer ∘ inner) original := by
  cases original with
  | empty => simp only [work]
  | combine left right =>
      simp only [work, work_comp outer inner left, work_comp outer inner right]
  | declareGroups groups tasks =>
      simp only [work, work_comp outer inner tasks, List.map_map]
      congr 2
      funext group
      exact fragment_comp outer inner group
  | executionGroup groups path result children =>
      simp only [work, work_comp outer inner children, List.map_map]
      congr 2
      funext group
      exact fragment_comp outer inner group
  | stream descriptor items =>
      simp only [work, node_comp, List.map_map]
      congr 1
      apply List.map_congr_left
      intro item member
      exact congrArg (fun children => (item.1, children)) (work_comp outer inner item.2)
termination_by sizeOf original
decreasing_by
  all_goals simp_wf
  all_goals try decreasing_trivial
  have smaller := List.sizeOf_lt_of_mem ‹item ∈ items›
  rcases item with ⟨result, children⟩
  simp only [Prod.mk.sizeOf_spec] at smaller
  dsimp only
  omega

-----------------------------------------------------------------------------------------
-- Exact traversal commutation includes invalid edges and all nested item work
-----------------------------------------------------------------------------------------

/-- Key renaming commutes with transparent declaration lookup. -/
@[simp]
theorem work_withoutDeclarations (keys : Nat → Nat) (original : Work)
    : (work keys original).withoutDeclarations
      = work keys original.withoutDeclarations := by
  cases original with
  | declareGroups groups tasks =>
      simpa only [work, Work.withoutDeclarations]
        using work_withoutDeclarations keys tasks
  | _ => simp only [work, Work.withoutDeclarations]
termination_by original

theorem child (keys : Nat → Nat) (original : WorkLocation) (address : Address)
    (index : Nat)
    : (location keys original).child? address index
      = (original.child? address index).map (location keys) := by
  rcases original with ⟨current, producer, owners⟩
  cases current with
  | empty | declareGroups =>
      simp only [location, work, WorkLocation.child?, Option.map_none]
  | combine left right =>
      cases index with
      | zero =>
          simp only [location, work, WorkLocation.child?, Option.map_some, work_withoutDeclarations]
      | succ index => cases index <;> simp only [location, work, WorkLocation.child?,
          Option.map_some, Option.map_none, work_withoutDeclarations]
  | executionGroup groups path result children =>
      cases index with
      | zero =>
          simp only [location, work, WorkLocation.child?, Option.map_some, group_keys, work_withoutDeclarations]
      | succ index => simp only [location, work, WorkLocation.child?, Option.map_none]
  | stream original items =>
      simp only [location, work, WorkLocation.child?, List.getElem?_map, Option.map_map,
        Function.comp_def, work_withoutDeclarations, List.map_nil]

theorem traverse (keys : Nat → Nat) (route : Address) (original : WorkLocation)
    (rest : Address)
    : locateWork.go route (location keys original) rest
      = (locateWork.go route original rest).map (location keys) := by
  induction rest generalizing route original with
  | nil => rfl
  | cons index rest ih =>
      simp only [locateWork.go, child]
      cases step : original.child? route index with
      | none => rfl
      | some next => exact ih (route ++ [index]) next

/-- Every structural lookup, including absence, is preserved at the same address. -/
theorem locate (keys : Nat → Nat) (original : Work) (address : Address)
    : locateWork (work keys original) address
      = (locateWork original address).map (location keys) := by
  simpa only [locateWork, location, List.map_nil, work_withoutDeclarations]
    using traverse keys [] ⟨original.withoutDeclarations, none, []⟩ address

theorem located {original address current producer owners}
    (found : Located original address current producer owners) (keys : Nat → Nat)
    : Located (work keys original) address (work keys current) producer
        (owners.map keys) := by
  unfold Located at found ⊢
  rw [locate, found]
  rfl

/-- Coverage is derived from the same exact lookup, not just forward preservation. -/
theorem located_original {original address current producer owners}
    (found : Located (work keys original) address current producer owners)
    : ∃ before enclosing,
        Located original address before producer enclosing
        ∧ work keys before = current
        ∧ enclosing.map keys = owners := by
  unfold Located at found
  rw [locate] at found
  obtain ⟨before, known, equal⟩ := Option.map_eq_some_iff.mp found
  rcases before with ⟨before, birth, enclosing⟩
  have producerEqual : birth = producer := congrArg WorkLocation.producer equal
  subst birth
  refine ⟨before, enclosing, known, congrArg WorkLocation.current equal,
    congrArg WorkLocation.owners equal⟩

-----------------------------------------------------------------------------------------
-- Task/node soundness and coverage retain payloads, producers and ordered dependencies
-----------------------------------------------------------------------------------------

theorem task {original occurrence owners producer value}
    (known : TaskAt original occurrence owners producer value) (keys : Nat → Nat)
    : TaskAt (work keys original) occurrence (owners.map keys) producer
        (payload keys value) := by
  cases StructuralEquivalence.taskAt_of_current known with
  | executionGroup found =>
      have renamed := located found.toCurrent keys
      simp only [work] at renamed
      simpa only [payload, group_keys] using TaskAt.executionGroup renamed
  | @item address descriptor items producer enclosing index result children found entry =>
      have renamed
          : (items.map (fun item => (item.1, work keys item.2)))[index]?
            = some (result, work keys children) := by
        rw [List.getElem?_map, entry]
        rfl
      have located := located found.toCurrent keys
      simp only [work] at located
      simpa only [payload, List.map_singleton, node] using TaskAt.item located renamed

theorem delivery_node {original descriptor kind dependencies producer}
    (known : NodeAt original descriptor kind dependencies producer) (keys : Nat → Nat)
    : NodeAt (work keys original) (node keys descriptor) kind (dependencies.map keys)
        producer := by
  cases StructuralEquivalence.nodeAt_of_current known with
  | group found member =>
      have renamed := located found.toCurrent keys
      simp only [work] at renamed
      simpa only [fragment, node, List.map_map, Function.comp_def]
        using NodeAt.group renamed (List.mem_map_of_mem member)
  | stream found =>
      have renamed := located found.toCurrent keys
      simp only [work] at renamed
      exact NodeAt.stream renamed

/-- Every renamed task has an original at that same occurrence and producer. -/
theorem task_original {original occurrence owners producer value}
    (known : TaskAt (work keys original) occurrence owners producer value)
    : ∃ before outcome,
        TaskAt original occurrence before producer outcome
        ∧ before.map keys = owners
        ∧ payload keys outcome = value := by
  cases occurrence with
  | executionGroup address =>
      obtain ⟨groups, path, result, children, enclosing, found, rfl, rfl⟩ := known
      obtain ⟨before, oldOwners, oldFound, same, _⟩ :=
        located_original (original := original) (keys := keys) found
      cases before with
      | empty | combine | stream | declareGroups => simp [work] at same
      | executionGroup originalGroups originalPath originalResult originalChildren =>
          simp only [work, Work.executionGroup.injEq] at same
          obtain ⟨rfl, rfl, rfl, rfl⟩ := same
          exact ⟨_, _, TaskAt.executionGroup oldFound, (group_keys keys originalGroups).symm, rfl⟩
  | item address index =>
      obtain ⟨descriptor, items, enclosing, result, children, found, entry, rfl, rfl⟩ := known
      obtain ⟨before, oldOwners, oldFound, same, _⟩ :=
        located_original (original := original) (keys := keys) found
      cases before with
      | empty | combine | executionGroup | declareGroups => simp [work] at same
      | stream originalNode originalItems =>
          simp only [work, Work.stream.injEq] at same
          obtain ⟨rfl, rfl⟩ := same
          rw [List.getElem?_map] at entry
          obtain ⟨⟨oldResult, oldChildren⟩, oldEntry, equal⟩ := Option.map_eq_some_iff.mp entry
          cases equal
          exact ⟨_, _, TaskAt.item oldFound oldEntry, rfl, rfl⟩

/-- Every renamed node descriptor has an original with the same dependency/producers. -/
theorem node_original {original descriptor kind dependencies producer}
    (known : NodeAt (work keys original) descriptor kind dependencies producer)
    : ∃ before parents,
        NodeAt original before kind parents producer
        ∧ node keys before = descriptor
        ∧ parents.map keys = dependencies := by
  cases kind with
  | group =>
      obtain ⟨address, groups, path, result, children, enclosing, selected, found,
        member, rfl, rfl⟩ := known
      obtain ⟨before, oldOwners, oldFound, same, _⟩ :=
        located_original (original := original) (keys := keys) found
      cases before with
      | empty | combine | stream | declareGroups => simp [work] at same
      | executionGroup originalGroups originalPath originalResult originalChildren =>
          simp only [work, Work.executionGroup.injEq] at same
          obtain ⟨rfl, rfl, rfl, rfl⟩ := same
          obtain ⟨oldGroup, oldMember, rfl⟩ := List.mem_map.mp member
          exact ⟨_, _, NodeAt.group oldFound oldMember, rfl, (ancestor_keys keys oldGroup).symm⟩
  | stream =>
      obtain ⟨address, items, found⟩ := known
      obtain ⟨before, oldOwners, oldFound, same, parents⟩ :=
        located_original (original := original) (keys := keys) found
      cases before with
      | empty | combine | executionGroup | declareGroups => simp [work] at same
      | stream originalNode originalItems =>
          simp only [work, Work.stream.injEq] at same
          obtain ⟨rfl, rfl⟩ := same
          exact ⟨_, _, NodeAt.stream oldFound, rfl, parents⟩

-----------------------------------------------------------------------------------------
-- Checked structural correspondence root (no execution policy or injectivity assumed)
-----------------------------------------------------------------------------------------

/-- The same key map preserves and covers structural lookups, tasks and delivery nodes.
This root does not assert that cancelling execution constructs such a map, or that a
noninjective map preserves distinct delivery identities.
-/
def StructuralKeyRenaming : Prop :=
  ∀ keys original,
    (∀ address,
      locateWork (work keys original) address
      = (locateWork original address).map (location keys))
    ∧ (∀ occurrence owners producer value,
        TaskAt (work keys original) occurrence owners producer value
        ↔ ∃ before outcome,
            TaskAt original occurrence before producer outcome
            ∧ before.map keys = owners
            ∧ payload keys outcome = value)
    ∧ (∀ descriptor kind dependencies producer,
        NodeAt (work keys original) descriptor kind dependencies producer
        ↔ ∃ before parents,
            NodeAt original before kind parents producer
            ∧ node keys before = descriptor
            ∧ parents.map keys = dependencies)

/-- Checked composition of traversal commutation and task/node soundness plus coverage. -/
theorem structuralKeyRenaming_holds : StructuralKeyRenaming := by
  intro keys original
  refine ⟨locate keys original, ?_, ?_⟩
  · intro occurrence owners producer value
    constructor
    · exact task_original (original := original) (keys := keys)
    · rintro ⟨before, outcome, known, rfl, rfl⟩
      exact task known keys
  · intro descriptor kind dependencies producer
    constructor
    · exact node_original (original := original) (keys := keys)
    · rintro ⟨before, parents, known, rfl, rfl⟩
      exact delivery_node known keys

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.KeyRenaming
