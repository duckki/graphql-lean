import Proofs.GraphQL.IncrementalDelivery.Semantics.Collection

/-! Field properties survive grouping and execution-plan partitioning. -/

namespace GraphQL.IncrementalDelivery.Semantics

open GraphQL.IncrementalDelivery.Execution

def GroupsSatisfy (property : FieldDetails → Prop) (groups : CollectedFieldsMap) : Prop :=
  ∀ group ∈ groups, ∀ field ∈ group.2, property field

theorem groupsSatisfy_add (property : FieldDetails → Prop)
    (group : Name × List FieldDetails) (groups : CollectedFieldsMap)
    (hg : ∀ field ∈ group.2, property field) (hs : GroupsSatisfy property groups)
    : GroupsSatisfy property (CollectedFieldsMap.addFieldSet group groups) := by
  induction groups with
  | nil => simpa [CollectedFieldsMap.addFieldSet, GroupsSatisfy] using hg
  | cons head rest ih =>
      have hh := hs head (by simp)
      have ht : GroupsSatisfy property rest := fun g h => hs g (by simp [h])
      rcases group with ⟨ref, fields⟩
      rcases head with ⟨name, existing⟩
      by_cases h : name == ref
      · simp only [CollectedFieldsMap.addFieldSet, h, ↓reduceIte]
        intro candidate hc field hf
        simp only [List.mem_cons] at hc
        rcases hc with rfl | hc
        · rcases List.mem_append.mp hf with hf | hf
          · exact hh field hf
          · exact hg field hf
        · exact ht candidate hc field hf
      · simpa [CollectedFieldsMap.addFieldSet, h, GroupsSatisfy] using And.intro hh (ih ht)

theorem groupsSatisfy_merge (property : FieldDetails → Prop)
    (left right : CollectedFieldsMap)
    (hl : GroupsSatisfy property left) (hr : GroupsSatisfy property right)
    : GroupsSatisfy property (CollectedFieldsMap.merge left right) := by
  induction right generalizing left with
  | nil => exact hl
  | cons group rest ih =>
      exact ih (CollectedFieldsMap.addFieldSet group left)
        (groupsSatisfy_add property group left (hr group (by simp)) hl)
        (fun g h => hr g (by simp [h]))

/-- Unlike RunMatches, this assertion permits the fresh-ref supply to advance. -/
def RunEnsures (property : α → Prop) (action : StateM NodeRef α) : Prop :=
  ∀ state, property (action.run state).1

theorem runEnsures_pure (property : α → Prop) (value : α) (h : property value)
    : RunEnsures property (pure value) :=
  fun _ => h

theorem runEnsures_bind (property : α → Prop) (target : β → Prop)
    (action : StateM NodeRef α) (next : α → StateM NodeRef β)
    (h : RunEnsures property action)
    (hn : ∀ value, property value → RunEnsures target (next value))
    : RunEnsures target (action >>= next) := by
  intro state
  exact hn _ (h state) (action.run state).2

end GraphQL.IncrementalDelivery.Semantics
