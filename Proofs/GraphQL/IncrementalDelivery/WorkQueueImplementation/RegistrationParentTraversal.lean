import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RegistrationCoverageCore

/-! Registration invariant induction with completed candidate-parent visits. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open WorkQueueSemantics (NodeRefs)

/-- Recursive installation can use a candidate parent's permanent registration.
The visited set contains only candidates, and pending ancestor calls have greater refs.
The fuel budget counts distinct visits; it imposes no bound on numeric creation refs.
-/
theorem State.addGroups.go_preserves_parentRegistered (property : State → Prop)
    (candidates : List Group)
    (ordered
      : ∀ group ∈ candidates,
          ∀ parent, group.parent = some parent → parent < group.node.ref)
    (install
      : ∀ current group,
          group ∈ candidates
          → current.LiveGroupsRegistered
          → (∀ parent,
              group.parent = some parent
              → parent ∈ candidates.map (fun group => group.node.ref)
              → parent ∈ current.registeredGroups)
          → property current
          → property (current.addGroup group))
    (fuel : Nat) (queue : State) (roots : List Execution.DeliveryNode)
    (visited : NodeRefs) (group : Group) (member : group ∈ candidates)
    (coverage : queue.LiveGroupsRegistered) (unique : visited.Nodup)
    (included : visited ⊆ candidates.map (fun group => group.node.ref))
    (budget : candidates.length < fuel + visited.length)
    (pending : ∀ ref ∈ visited, ref ∉ queue.registeredGroups → group.node.ref < ref)
    (valid : property queue)
    : property (State.addGroups.go candidates fuel (queue, roots, visited) group).1 := by
  induction fuel generalizing queue roots visited group with
  | zero =>
      have bound := unique.length_le_of_subset included
      simp only [List.length_map] at bound
      omega
  | succ fuel ih =>
      simp only [State.addGroups.go]
      split
      · exact valid
      · rename_i unseen
        have fresh : group.node.ref ∉ visited := by simpa using unseen
        split
        · exact valid
        · let marked := visited ++ [group.node.ref]
          have markedUnique : marked.Nodup := by
            apply List.nodup_append.mpr
            refine ⟨unique, by simp, ?_⟩
            intro first seen second single same
            cases List.mem_singleton.mp single
            exact fresh (same ▸ seen)
          have markedIncluded : marked ⊆ candidates.map (fun group => group.node.ref) := by
            intro ref seen
            rcases List.mem_append.mp seen with old | new
            · exact included old
            · cases List.mem_singleton.mp new
              exact List.mem_map.mpr ⟨group, member, rfl⟩
          have nextBudget : candidates.length < fuel + marked.length := by
            simp only [marked, List.length_append, List.length_singleton]
            omega
          split
          · rename_i absent
            apply install queue group member coverage _ valid
            intro parent parentEq candidate
            obtain ⟨prior, priorMember, identity⟩ := List.mem_map.mp candidate
            have missing : candidates.find? (fun other => other.node.ref == parent) = none := by
              simpa only [parentEq, Option.bind_some] using absent
            exact False.elim (List.find?_eq_none.mp missing prior priorMember
              (beq_iff_eq.mpr identity))
          · rename_i parent found
            obtain ⟨ref, parentEq, selected⟩ := Option.bind_eq_some_iff.mp found
            have parentMember := List.mem_of_find?_eq_some selected
            have identity : parent.node.ref = ref := beq_iff_eq.mp (List.find?_some (p := fun candidate : Group => candidate.node.ref == ref) selected)
            have smaller : parent.node.ref < group.node.ref :=
              identity ▸ ordered group member ref parentEq
            have parentPending : ∀ ref ∈ marked,
                ref ∉ queue.registeredGroups → parent.node.ref < ref := by
              intro other seen unregistered
              rcases List.mem_append.mp seen with old | new
              · exact Nat.lt_trans smaller (pending other old unregistered)
              · cases List.mem_singleton.mp new
                exact smaller
            have nextValid := ih queue roots marked parent parentMember coverage markedUnique
              markedIncluded nextBudget parentPending valid
            have prepared := State.addGroups.go_registration candidates fuel queue roots marked parent coverage
            have fuelPositive : 0 < fuel := by
              have bound := markedUnique.length_le_of_subset markedIncluded
              simp only [List.length_map] at bound
              omega
            apply install _ group member prepared.1 _ nextValid
            intro actual actualEq _
            have same : actual = ref := Option.some.inj (actualEq.symm.trans parentEq)
            subst actual
            rw [← identity]
            rcases prepared.2.2.2 fuelPositive with installed | seen
            · exact installed
            · apply Classical.byContradiction
              intro absent
              have impossible := parentPending parent.node.ref seen (fun registered => absent (prepared.2.1 registered))
              exact Nat.lt_irrefl _ impossible

/-- A traversal visits only its supplied candidates, without repeating refs. -/
theorem State.addGroups.go_visited (candidates : List Group) (fuel : Nat)
    (acc : State × List Execution.DeliveryNode × NodeRefs) (group : Group)
    (member : group ∈ candidates) (unique : acc.2.2.Nodup)
    (included : acc.2.2 ⊆ candidates.map (fun group => group.node.ref))
    : (State.addGroups.go candidates fuel acc group).2.2.Nodup
      ∧ (State.addGroups.go candidates fuel acc group).2.2
        ⊆ candidates.map (fun group => group.node.ref) := by
  induction fuel generalizing acc group with
  | zero => exact ⟨unique, included⟩
  | succ fuel ih =>
      rcases acc with ⟨current, roots, visited⟩
      simp only [State.addGroups.go]
      split
      · exact ⟨unique, included⟩
      · rename_i unseen
        have fresh : group.node.ref ∉ visited := by simpa using unseen
        have markedUnique : (visited ++ [group.node.ref]).Nodup := by
          apply List.nodup_append.mpr
          refine ⟨unique, by simp, ?_⟩
          intro first seen second single same
          cases List.mem_singleton.mp single
          exact fresh (same ▸ seen)
        have markedIncluded : visited ++ [group.node.ref]
            ⊆ candidates.map (fun group => group.node.ref) := by
          intro ref seen
          rcases List.mem_append.mp seen with old | new
          · exact included old
          · cases List.mem_singleton.mp new
            exact List.mem_map.mpr ⟨group, member, rfl⟩
        split
        · exact ⟨markedUnique, markedIncluded⟩
        · split
          · exact ⟨markedUnique, markedIncluded⟩
          · rename_i parent found
            obtain ⟨ref, _, selected⟩ := Option.bind_eq_some_iff.mp found
            exact ih _ parent (List.mem_of_find?_eq_some selected) markedUnique markedIncluded

/-- Every actual installation may use prior registration of candidate parents.
Creation refs justify acyclic parent traversal; candidate encounter order remains arbitrary.
-/
theorem State.addGroups_preserves_parentRegistered (property : State → Prop)
    (groups : List Group)
    (ordered
      : ∀ group ∈ groups, ∀ parent, group.parent = some parent → parent < group.node.ref)
    (install
      : ∀ current group,
          group ∈ groups
          → current.LiveGroupsRegistered
          → (∀ parent,
              group.parent = some parent
              → parent ∈ groups.map (fun group => group.node.ref)
              → parent ∈ current.registeredGroups)
          → property current
          → property (current.addGroup group))
    (queue : State) (coverage : queue.LiveGroupsRegistered) (valid : property queue)
    : property (queue.addGroups groups).1 := by
  let step := fun acc group => State.addGroups.go groups (groups.length + 1) acc group
  have loop (more : List Group) (subset : more ⊆ groups)
      (current : State) (roots : List Execution.DeliveryNode) (visited : NodeRefs)
      (coverage : current.LiveGroupsRegistered) (unique : visited.Nodup)
      (included : visited ⊆ groups.map (fun group => group.node.ref))
      (known : visited ⊆ current.registeredGroups) (valid : property current)
      : property (more.foldl step (current, roots, visited)).1 := by
    induction more generalizing current roots visited with
    | nil => exact valid
    | cons group rest ih =>
        have member : group ∈ groups := subset List.mem_cons_self
        let next := step (current, roots, visited) group
        have registered := State.addGroups.go_registration groups (groups.length + 1)
          current roots visited group coverage
        have visits := State.addGroups.go_visited groups (groups.length + 1)
          (current, roots, visited) group member unique included
        have nextValid := State.addGroups.go_preserves_parentRegistered property groups ordered
          install (groups.length + 1) current roots visited group member coverage unique included
          (by omega) (fun ref seen absent => False.elim (absent (known seen))) valid
        exact ih (fun _ member => subset (List.mem_cons_of_mem _ member)) next.1 next.2.1
          next.2.2 registered.1 visits.1 visits.2
          (fun ref member =>
            (registered.2.2.1 ref member).elim id (fun old => registered.2.1 (known old)))
          nextValid
  exact loop groups (List.Subset.refl _) queue [] [] coverage (by simp) (by simp)
    (by simp) valid

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
