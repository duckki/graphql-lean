import GraphQL.IncrementalDelivery.WorkQueueImplementation

/-! Invariant induction for recursive, parent-first group registration. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open WorkQueueSemantics (NodeRefs)

/-- A single installation registers only its supplied ref. -/
theorem State.addGroup_registeredGroups_subset (queue : State) (group : Group)
    : (queue.addGroup group).registeredGroups
      ⊆ queue.registeredGroups ++ [group.node.ref] := by
  unfold State.addGroup
  split
  · exact List.subset_append_left _ _
  · split
    · exact List.Subset.refl _
    · split
      · split <;> exact List.Subset.refl _
      · exact List.Subset.refl _

/-- Installation retains every earlier permanent group registration. -/
theorem State.addGroup_registeredGroups_subset_old (queue : State) (group : Group)
    : queue.registeredGroups ⊆ (queue.addGroup group).registeredGroups := by
  unfold State.addGroup
  split
  · exact List.Subset.refl _
  · split
    · exact List.subset_append_left _ _
    · split
      · split <;> exact List.subset_append_left _ _
      · exact List.subset_append_left _ _

/-- Every recursive registration step preserves a state invariant preserved by installation. -/
theorem State.addGroups.go_preserves (property : State → Prop) (candidates : List Group)
    (install
      : ∀ current group,
          group ∈ candidates → property current → property (current.addGroup group))
    (fuel : Nat) (acc : State × List Execution.DeliveryNode × NodeRefs) (group : Group)
    (member : group ∈ candidates) (valid : property acc.1)
    : property (State.addGroups.go candidates fuel acc group).1 := by
  induction fuel generalizing acc group with
  | zero => exact valid
  | succ fuel ih =>
      rcases acc with ⟨current, roots, visited⟩
      simp only [State.addGroups.go]
      split
      · exact valid
      · split
        · exact valid
        · split
          · exact install current group member valid
          · rename_i parent found
            obtain ⟨ref, _, selected⟩ := Option.bind_eq_some_iff.mp found
            have parentMember := List.mem_of_find?_eq_some selected
            exact install _ group member (ih _ parent parentMember valid)

/-- Parent-first registration preserves any invariant preserved by each candidate install. -/
theorem State.addGroups_preserves (property : State → Prop) (groups : List Group)
    (install
      : ∀ current group,
          group ∈ groups → property current → property (current.addGroup group))
    (queue : State) (valid : property queue)
    : property (queue.addGroups groups).1 := by
  let step := fun acc group => State.addGroups.go groups (groups.length + 1) acc group
  have fold (more : List Group) (included : more ⊆ groups)
      (acc : State × List Execution.DeliveryNode × NodeRefs) (valid : property acc.1)
      : property (more.foldl step acc).1 := by
    induction more generalizing acc with
    | nil => exact valid
    | cons group rest ih =>
        exact ih (fun _ member => included (List.mem_cons_of_mem _ member)) _
          (State.addGroups.go_preserves property groups install _ acc group
            (included (by simp)) valid)
  exact fold groups (List.Subset.refl _) (queue, [], []) valid

/-- Registration preserves any field untouched by individual group installation. -/
theorem State.addGroups_projection {α : Type} (project : State → α)
    (preserved : ∀ current group, project (current.addGroup group) = project current)
    (queue : State) (groups : List Group)
    : project (queue.addGroups groups).1 = project queue := by
  exact State.addGroups_preserves (fun current => project current = project queue) groups
    (fun current group _ same => (preserved current group).trans same) queue rfl

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
