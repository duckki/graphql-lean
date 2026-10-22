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

/-- Every fresh canonical parentless candidate appears in the installed root frontier.
Witness: a root's first installation appends its ref, and permanent registration prevents
a later visit from consuming that ref without retaining its root entry.
-/
theorem State.addGroups_parentless_candidate (queue : State) (groups : List Group)
    (registered : queue.LiveGroupsRegistered) {parents : Nat → NodeRefs}
    (canonical
      : ∀ candidate ∈ groups, candidate.parent = (parents candidate.node.ref).head?)
    {group : Group} (member : group ∈ groups) (parentless : group.parent = none)
    (fresh : group.node.ref ∉ queue.registeredGroups)
    (_absent : queue.groupNode? group.node.ref = none)
    : group.node.ref ∈ (queue.addGroups groups).2.map Execution.DeliveryNode.ref := by
  let property (acc : State × List Execution.DeliveryNode × NodeRefs) :=
    acc.1.LiveGroupsRegistered ∧ (group.node.ref ∈ acc.1.registeredGroups →
      group.node.ref ∈ acc.2.1.map Execution.DeliveryNode.ref)
  have visit (fuel : Nat) (acc : State × List Execution.DeliveryNode × NodeRefs)
      (candidate : Group) (included : candidate ∈ groups) (prior : property acc)
      : property (State.addGroups.go groups fuel acc candidate) := by
    induction fuel generalizing acc candidate with
    | zero => exact prior
    | succ fuel ih =>
        obtain ⟨current, roots, visited⟩ := acc
        simp only [State.addGroups.go]
        split
        · exact prior
        · split
          · exact prior
          · by_cases same : candidate.node.ref = group.node.ref
            · have noParent : candidate.parent = none := by
                rw [canonical candidate included, same, ← canonical group member, parentless]
              simp only [noParent, Option.bind_none, Option.isNone_none, ite_true]
              exact ⟨prior.1.addGroup candidate, fun _ => by simp [same]⟩
            · have finish (state : State) (roots : List Execution.DeliveryNode) (visited : NodeRefs)
                  (valid : property (state, roots, visited))
                  : property (state.addGroup candidate,
                    if candidate.parent.isNone then roots ++ [candidate.node] else roots, visited) := by
                refine ⟨valid.1.addGroup candidate, ?_⟩
                intro registered
                have old : group.node.ref ∈ state.registeredGroups := by
                  rcases List.mem_append.mp
                    (state.addGroup_registeredGroups_subset candidate registered) with old | new
                  · exact old
                  · exact False.elim (same (List.mem_singleton.mp new).symm)
                have covered := valid.2 old
                split
                · rw [List.map_append]
                  exact List.mem_append_left _ covered
                · exact covered
              split
              · exact finish current roots (visited ++ [candidate.node.ref]) prior
              · rename_i parent found
                obtain ⟨ref, _, selected⟩ := Option.bind_eq_some_iff.mp found
                exact finish _ _ _ (ih _ parent (List.mem_of_find?_eq_some selected) prior)
  have loop (more : List Group) (included : more ⊆ groups)
      (acc : State × List Execution.DeliveryNode × NodeRefs) (prior : property acc)
      : property (more.foldl
          (fun acc candidate => State.addGroups.go groups (groups.length + 1) acc candidate) acc) := by
    induction more generalizing acc with
    | nil => exact prior
    | cons candidate rest ih =>
        exact ih (fun _ member => included (List.mem_cons_of_mem _ member)) _
          (visit _ acc candidate (included List.mem_cons_self) prior)
  have final := loop groups (List.Subset.refl _) (queue, [], [])
    ⟨registered, fun known => False.elim (fresh known)⟩
  exact final.2 ((queue.addGroups_registration registered groups).2.2 group member)

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
