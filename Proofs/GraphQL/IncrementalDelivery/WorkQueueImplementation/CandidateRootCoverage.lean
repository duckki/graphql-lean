import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ParentLinkUpdates
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupFrontierUniqueness

/-! Complete finite parent chains connect integrated candidates to their parentless frontier. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- First-encounter deduplication retains each candidate ref
-----------------------------------------------------------------------------------------

/-- Deduplicating descriptors by first encounter never discards a delivery ref.
Witness: the selection fold retains old refs and either finds or appends each new ref.
Equal-ref descriptors need not be identical for this ref-only statement.
-/
theorem distinctDeliveryNodes_ref_covered (nodes : List Execution.DeliveryNode)
    {node : Execution.DeliveryNode} (member : node ∈ nodes)
    : node.ref ∈ (distinctDeliveryNodes nodes).map Execution.DeliveryNode.ref := by
  let step (selected : List Execution.DeliveryNode) (next : Execution.DeliveryNode) :=
    if selected.any (fun known => known.ref == next.ref) then selected else selected ++ [next]
  have loop (more selected : List Execution.DeliveryNode)
      : ∀ ref ∈ (selected ++ more).map Execution.DeliveryNode.ref,
          ref ∈ (more.foldl step selected).map Execution.DeliveryNode.ref := by
    induction more generalizing selected with
    | nil => simp
    | cons next rest ih =>
        intro ref included
        apply ih
        dsimp only [step]
        split
        · rename_i already
          obtain ⟨known, present, same⟩ := List.any_eq_true.mp already
          rcases List.mem_map.mp included with ⟨entry, member, rfl⟩
          rcases List.mem_append.mp member with prior | later
          · exact List.mem_map_of_mem (List.mem_append_left _ prior)
          · rcases List.mem_cons.mp later with rfl | tail
            · exact List.mem_map.mpr ⟨known, List.mem_append_left _ present, beq_iff_eq.mp same⟩
            · exact List.mem_map_of_mem (List.mem_append_right _ tail)
        · simpa only [List.append_assoc, List.singleton_append] using included
  exact loop nodes [] node.ref (List.mem_map_of_mem member)

/-- Every fresh parentless descriptor contributes its ref to the actual candidate frontier.
Witness: the two registration filters and ref retention through first-encounter deduplication.
-/
theorem State.addGroups_parentless_candidate (queue : State) (groups : List Group)
    {group : Group} (member : group ∈ groups) (parentless : group.parent = none)
    (fresh : group.node.ref ∉ queue.registeredGroups)
    (absent : queue.groupNode? group.node.ref = none)
    : group.node.ref ∈ (queue.addGroups groups).2.map Execution.DeliveryNode.ref := by
  apply distinctDeliveryNodes_ref_covered
  apply List.mem_filterMap.mpr
  exact ⟨group, by simp [member, fresh, absent], by simp [parentless]⟩

-----------------------------------------------------------------------------------------
-- Following complete live parent links terminates at a represented root
-----------------------------------------------------------------------------------------

/-- A live parent-closed candidate family is covered by its parentless root refs.
Witness: strict delivery-ref descent follows complete stored parent links; each recursive
parent is another candidate and is live. The base case is a supplied parentless root.
This is a local concrete forest theorem, not a scheduler or source assumption.
-/
theorem State.ParentLinksComplete.candidates_root_coverage {queue : State} {parents}
    (links : queue.ParentLinksComplete parents) (forest : queue.RemovalForest parents)
    (candidates : List Group) (roots : NodeRefs)
    (canonical : ∀ group ∈ candidates, group.parent = (parents group.node.ref).head?)
    (parentCovered
      : ∀ group ∈ candidates,
          ∀ parent,
            group.parent = some parent → ∃ next ∈ candidates, next.node.ref = parent)
    (live : ∀ group ∈ candidates, ∃ node, queue.groupNode? group.node.ref = some node)
    (rootCovered : ∀ group ∈ candidates, group.parent = none → group.node.ref ∈ roots)
    {group : Group} (member : group ∈ candidates)
    : ∃ root ∈ roots, queue.LiveDescendant root group.node.ref := by
  have walk (ref : NodeRef) : ∀ candidate ∈ candidates, candidate.node.ref = ref
      → ∃ root ∈ roots, queue.LiveDescendant root ref := by
    induction ref using Nat.strongRecOn with
    | ind ref ih =>
        intro candidate included same
        obtain ⟨child, childFound⟩ := live candidate included
        have childRef := State.groupNode?_ref childFound
        cases parentEq : candidate.parent with
        | none =>
            exact ⟨ref, same ▸ rootCovered candidate included parentEq, same ▸ .self childFound⟩
        | some parent =>
            obtain ⟨ancestor, ancestorMember, ancestorRef⟩ :=
              parentCovered candidate included parent parentEq
            obtain ⟨node, found⟩ := live ancestor ancestorMember
            have nodeRef := (State.groupNode?_ref found).trans ancestorRef
            have edge := links child (List.mem_of_find?_eq_some childFound) node
              (List.mem_of_find?_eq_some found)
              (by rw [childRef, ← canonical candidate included, parentEq, nodeRef])
            have lower := forest.increasing (List.mem_of_find?_eq_some found)
              (List.mem_of_find?_eq_some childFound) edge
            rw [nodeRef, childRef, same] at lower
            obtain ⟨root, active, path⟩ := ih parent lower ancestor ancestorMember ancestorRef
            refine ⟨root, active, path.trans ?_⟩
            exact .child (ancestorRef ▸ found) (childRef.trans same ▸ edge)
              (same ▸ .self childFound)
  exact walk group.node.ref group member rfl

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
