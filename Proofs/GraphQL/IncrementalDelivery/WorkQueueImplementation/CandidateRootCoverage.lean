import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ParentLinkUpdates
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupFrontierUniqueness

/-! Complete finite parent chains connect integrated candidates to their parentless frontier. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- First-encounter deduplication retains each candidate key
-----------------------------------------------------------------------------------------

/-- Deduplicating descriptors by first encounter never discards a delivery key.
Witness: the selection fold retains old keys and either finds or appends each new key.
Equal-key descriptors need not be identical for this key-only statement.
-/
theorem distinctDeliveryNodes_key_covered (nodes : List Execution.DeliveryNode)
    {node : Execution.DeliveryNode} (member : node ∈ nodes)
    : node.key ∈ (distinctDeliveryNodes nodes).map Execution.DeliveryNode.key := by
  let step (selected : List Execution.DeliveryNode) (next : Execution.DeliveryNode) :=
    if selected.any (fun known => known.key == next.key) then selected else selected ++ [next]
  have loop (more selected : List Execution.DeliveryNode)
      : ∀ key ∈ (selected ++ more).map Execution.DeliveryNode.key,
          key ∈ (more.foldl step selected).map Execution.DeliveryNode.key := by
    induction more generalizing selected with
    | nil => simp
    | cons next rest ih =>
        intro key included
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
  exact loop nodes [] node.key (List.mem_map_of_mem member)

/-- Every fresh parentless descriptor contributes its key to the actual candidate frontier.
Witness: the two registration filters and key retention through first-encounter deduplication.
-/
theorem State.addGroups_parentless_candidate (queue : State) (groups : List Group)
    {group : Group} (member : group ∈ groups) (parentless : group.parent = none)
    (fresh : group.node.key ∉ queue.registeredGroups)
    (absent : queue.groupNode? group.node.key = none)
    : group.node.key ∈ (queue.addGroups groups).2.map Execution.DeliveryNode.key := by
  apply distinctDeliveryNodes_key_covered
  apply List.mem_filterMap.mpr
  exact ⟨group, by simp [member, fresh, absent], by simp [parentless]⟩

-----------------------------------------------------------------------------------------
-- Following complete live parent links terminates at a represented root
-----------------------------------------------------------------------------------------

/-- A live parent-closed candidate family is covered by its parentless root keys.
Witness: strict delivery-key descent follows complete stored parent links; each recursive
parent is another candidate and is live. The base case is a supplied parentless root.
This is a local concrete forest theorem, not a scheduler or source assumption.
-/
theorem State.ParentLinksComplete.candidates_root_coverage {queue : State} {parents}
    (links : queue.ParentLinksComplete parents) (forest : queue.RemovalForest parents)
    (candidates : List Group) (roots : Keys)
    (canonical : ∀ group ∈ candidates, group.parent = (parents group.node.key).head?)
    (parentCovered
      : ∀ group ∈ candidates,
          ∀ parent,
            group.parent = some parent → ∃ next ∈ candidates, next.node.key = parent)
    (live : ∀ group ∈ candidates, ∃ node, queue.groupNode? group.node.key = some node)
    (rootCovered : ∀ group ∈ candidates, group.parent = none → group.node.key ∈ roots)
    {group : Group} (member : group ∈ candidates)
    : ∃ root ∈ roots, queue.LiveDescendant root group.node.key := by
  have walk (key : Nat) : ∀ candidate ∈ candidates, candidate.node.key = key
      → ∃ root ∈ roots, queue.LiveDescendant root key := by
    induction key using Nat.strongRecOn with
    | ind key ih =>
        intro candidate included same
        obtain ⟨child, childFound⟩ := live candidate included
        have childKey := State.groupNode?_key childFound
        cases parentEq : candidate.parent with
        | none =>
            exact ⟨key, same ▸ rootCovered candidate included parentEq, same ▸ .self childFound⟩
        | some parent =>
            obtain ⟨ancestor, ancestorMember, ancestorKey⟩ :=
              parentCovered candidate included parent parentEq
            obtain ⟨node, found⟩ := live ancestor ancestorMember
            have nodeKey := (State.groupNode?_key found).trans ancestorKey
            have edge := links child (List.mem_of_find?_eq_some childFound) node
              (List.mem_of_find?_eq_some found)
              (by rw [childKey, ← canonical candidate included, parentEq, nodeKey])
            have lower := forest.increasing (List.mem_of_find?_eq_some found)
              (List.mem_of_find?_eq_some childFound) edge
            rw [nodeKey, childKey, same] at lower
            obtain ⟨root, active, path⟩ := ih parent lower ancestor ancestorMember ancestorKey
            refine ⟨root, active, path.trans ?_⟩
            exact .child (ancestorKey ▸ found) (childKey.trans same ▸ edge)
              (same ▸ .self childFound)
  exact walk group.node.key group member rfl

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
