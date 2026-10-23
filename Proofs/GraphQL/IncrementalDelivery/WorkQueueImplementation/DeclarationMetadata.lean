import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.WorkDeclarations
import Proofs.GraphQL.IncrementalDelivery.Semantics.MixedWorkRefs
import Proofs.GraphQL.IncrementalDelivery.Semantics.RefRoles
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.DescriptorMetadata

/-! Proof-only metadata inventory covers explicit declarations and task contributors.
It does not assign task ownership to unused declarations or ancestor-only records.
-/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue.GroupMetadata
open GraphQL.IncrementalDelivery.Execution WorkQueueSemantics

/-- All declared and contributing fragments, including metadata behind future tasks/items. -/
def fragments : Execution.Work → List DeferredFragment
  | .empty => []
  | .combine left right => fragments left ++ fragments right
  | .declareGroups groups tasks => groups ++ fragments tasks
  | .executionGroup groups _ _ children => groups ++ fragments children
  | .stream _ items => items.flatMap (fun item => fragments item.2)
termination_by work => sizeOf work
decreasing_by
  all_goals subst_vars; simp_wf
  all_goals try decreasing_trivial
  have smaller := List.sizeOf_lt_of_mem ‹item ∈ items›
  rcases item with ⟨result, children⟩
  simp only [Prod.mk.sizeOf_spec] at smaller
  dsimp only
  omega

/-- Address normalization may hide outer declarations but cannot invent metadata. -/
theorem fragments_withoutDeclarations (work : Execution.Work)
    : (fragments work.withoutDeclarations).Subset (fragments work) := by
  cases work with
  | declareGroups groups tasks =>
      intro fragment member
      rw [fragments]
      exact List.mem_append_right _ (fragments_withoutDeclarations tasks member)
  | _ => intro fragment member; exact member
termination_by work

/-- Every structurally located boundary retains its metadata in the original work. -/
theorem located_fragments {root address current producer owners}
    (located : Located root address current producer owners)
    : (fragments current).Subset (fragments root) := by
  have navigation := StructuralEquivalence.located_of_current located
  clear located
  induction navigation with
  | root => exact fragments_withoutDeclarations root
  | left _ ih =>
      intro fragment member
      apply ih
      rw [fragments]
      exact List.mem_append_left _ (fragments_withoutDeclarations _ member)
  | right _ ih =>
      intro fragment member
      apply ih
      rw [fragments]
      exact List.mem_append_right _ (fragments_withoutDeclarations _ member)
  | executionGroup _ ih =>
      intro fragment member
      apply ih
      rw [fragments]
      exact List.mem_append_right _ (fragments_withoutDeclarations _ member)
  | item _ entry ih =>
      intro fragment member
      apply ih
      rw [fragments]
      exact List.mem_flatMap.mpr
        ⟨_, List.mem_of_getElem? entry, fragments_withoutDeclarations _ member⟩

/-- A task's raw child work retains declarations hidden by normalized address lookup. -/
theorem executionGroup_children {root address groups path result children producer owners}
    (located
      : Located root address (.executionGroup groups path result children) producer
          owners)
    : (fragments children).Subset (fragments root) := by
  intro fragment member
  apply located_fragments located
  rw [fragments]
  exact List.mem_append_right _ member

/-- The selected stream item's raw children retain their declaration inventory. -/
theorem item_children {root address node items producer owners result children}
    {index : Nat} (located : Located root address (.stream node items) producer owners)
    (entry : items[index]? = some (result, children))
    : (fragments children).Subset (fragments root) := by
  intro fragment member
  apply located_fragments located
  rw [fragments]
  exact List.mem_flatMap.mpr ⟨_, List.mem_of_getElem? entry, member⟩

end GraphQL.IncrementalDelivery.ReferenceWorkQueue.GroupMetadata

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue.GroupMetadata
open GraphQL.IncrementalDelivery.Execution

/-- Every declared or contributing fragment has the execution's bounded ancestry. -/
theorem fragmentAt {parents lower bound} {work : Execution.Work}
    (known : Semantics.MixedRefs.WorkAt parents lower bound work)
    {fragment : DeferredFragment} (member : fragment ∈ fragments work)
    : Semantics.Ancestry.FragmentAt parents bound fragment := by
  cases work with
  | empty => simp [fragments] at member
  | combine left right =>
      rw [Semantics.MixedRefs.WorkAt] at known
      rw [fragments] at member
      rcases List.mem_append.mp member with first | second
      · exact fragmentAt known.1 first
      · exact fragmentAt known.2 second
  | declareGroups groups tasks =>
      rw [Semantics.MixedRefs.WorkAt] at known
      rw [fragments] at member
      rcases List.mem_append.mp member with declared | nested
      · exact known.1 fragment declared
      · exact fragmentAt known.2 nested
  | executionGroup groups path result children =>
      rw [Semantics.MixedRefs.WorkAt] at known
      rw [fragments] at member
      rcases List.mem_append.mp member with contributing | nested
      · exact (known.2.1 fragment contributing).2
      · exact fragmentAt known.2.2 nested
  | stream node items =>
      rw [Semantics.MixedRefs.WorkAt] at known
      rw [fragments] at member
      obtain ⟨item, selected, nested⟩ := List.mem_flatMap.mp member
      exact fragmentAt (known.2.2 item selected) nested
termination_by sizeOf work
decreasing_by
  all_goals subst_vars; simp_wf
  all_goals try decreasing_trivial
  have smaller := List.sizeOf_lt_of_mem selected
  rcases item with ⟨result, children⟩
  simp only [Prod.mk.sizeOf_spec] at smaller
  dsimp only
  omega

/-- Descriptor assignments cover explicit declarations as well as task-owned metadata. -/
theorem fragmentDescriptor {nodes bound} {work : Execution.Work}
    (known : DescriptorMetadata.WorkAt nodes bound work)
    {fragment : DeferredFragment} (member : fragment ∈ fragments work)
    : ∀ node ∈ fragment.node :: fragment.ancestors,
        DescriptorMetadata.Assigned nodes bound node := by
  cases work with
  | empty => simp [fragments] at member
  | combine left right =>
      rw [DescriptorMetadata.WorkAt] at known
      rw [fragments] at member
      rcases List.mem_append.mp member with first | second
      · exact fragmentDescriptor known.1 first
      · exact fragmentDescriptor known.2 second
  | declareGroups groups tasks | executionGroup groups _ _ tasks =>
      rw [DescriptorMetadata.WorkAt] at known
      rw [fragments] at member
      rcases List.mem_append.mp member with declared | nested
      · intro node within
        exact known.1 node (List.mem_flatMap.mpr ⟨fragment, declared, within⟩)
      · exact fragmentDescriptor known.2 nested
  | stream node items =>
      rw [DescriptorMetadata.WorkAt] at known
      rw [fragments] at member
      obtain ⟨item, selected, nested⟩ := List.mem_flatMap.mp member
      exact fragmentDescriptor (known.2 item selected) nested
termination_by sizeOf work
decreasing_by
  all_goals subst_vars; simp_wf
  all_goals try decreasing_trivial
  have smaller := List.sizeOf_lt_of_mem selected
  rcases item with ⟨result, children⟩
  simp only [Prod.mk.sizeOf_spec] at smaller
  dsimp only
  omega

/-- Declarations and contributor metadata retain defer role, including ancestor records. -/
theorem fragmentRoles {roles} {work : Execution.Work}
    (known : Semantics.RefRoles.WorkRoles roles work)
    {fragment : DeferredFragment} (member : fragment ∈ fragments work)
    : roles fragment.node.ref = false
      ∧ ∀ ancestor ∈ fragment.ancestors, roles ancestor.ref = false := by
  cases work with
  | empty => simp [fragments] at member
  | combine left right =>
      rw [Semantics.RefRoles.WorkRoles] at known
      rw [fragments] at member
      rcases List.mem_append.mp member with first | second
      · exact fragmentRoles known.1 first
      · exact fragmentRoles known.2 second
  | declareGroups groups tasks | executionGroup groups _ _ tasks =>
      rw [Semantics.RefRoles.WorkRoles] at known
      rw [fragments] at member
      rcases List.mem_append.mp member with declared | nested
      · exact known.1 fragment declared
      · exact fragmentRoles known.2 nested
  | stream node items =>
      rw [Semantics.RefRoles.WorkRoles] at known
      rw [fragments] at member
      obtain ⟨item, selected, nested⟩ := List.mem_flatMap.mp member
      exact fragmentRoles (known.2 item selected) nested
termination_by sizeOf work
decreasing_by
  all_goals subst_vars; simp_wf
  all_goals try decreasing_trivial
  have smaller := List.sizeOf_lt_of_mem selected
  rcases item with ⟨result, children⟩
  simp only [Prod.mk.sizeOf_spec] at smaller
  dsimp only
  omega

end GraphQL.IncrementalDelivery.ReferenceWorkQueue.GroupMetadata
