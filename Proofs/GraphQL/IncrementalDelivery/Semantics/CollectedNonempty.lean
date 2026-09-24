import Proofs.GraphQL.IncrementalDelivery.Semantics.Planning

/-! Collection never creates a response-name group without field occurrences.
This excludes empty deferred task groups when execution plans classify collected fields.
The result holds for arbitrary inherited usage and directive conditions.
-/

namespace GraphQL.IncrementalDelivery.Semantics

open GraphQL.IncrementalDelivery.Execution

attribute [local simp] id_pure_eq id_bind_eq id_map_eq run_bind run_map

def GroupsNonempty (groups : CollectedFieldsMap) : Prop :=
  ∀ group ∈ groups, group.2 ≠ []

theorem groupsNonempty_add (group : Name × List ExecutableField)
    (groups : CollectedFieldsMap) (hg : group.2 ≠ []) (hs : GroupsNonempty groups)
    : GroupsNonempty (addExecutableGroup group groups) := by
  induction groups with
  | nil => simpa [addExecutableGroup, GroupsNonempty] using hg
  | cons head rest ih =>
      have hh := hs head (by simp)
      have ht : GroupsNonempty rest := fun g hm => hs g (List.mem_cons_of_mem head hm)
      simp only [addExecutableGroup]
      split
      · intro next hn
        rcases List.mem_cons.mp hn with rfl | hn
        · simpa using fun he : head.2 ++ group.2 = [] => hh (List.append_eq_nil_iff.mp he).1
        · exact ht next hn
      · exact fun next hn => (List.mem_cons.mp hn).elim
          (fun he => he ▸ hh) (fun he => ih ht next he)

theorem groupsNonempty_merge (left right : CollectedFieldsMap)
    (hl : GroupsNonempty left) (hr : GroupsNonempty right)
    : GroupsNonempty (mergeExecutableGroups left right) := by
  induction right generalizing left with
  | nil => exact hl
  | cons group rest ih =>
      exact ih _ (groupsNonempty_add group left (hr group (by simp)) hl)
        (fun g hg => hr g (List.mem_cons_of_mem group hg))

mutual
  theorem collectSelection_nonempty (schema : Schema) (variables : VariableValues)
      (parentType : Name) (source : ResolverValue ObjectRef) (selection : Selection)
      (usage : Option DeferUsage) (state : Nat)
      : GroupsNonempty
          ((collectSelection schema variables parentType source usage selection).run
            state).1.fields := by
    cases selection with
    | field name fieldName arguments directives children =>
        cases ha : selectionDirectivesAllowBool variables directives <;>
          simp [collectSelection, ha, GroupsNonempty]
    | inlineFragment condition directives children =>
        cases ha : selectionDirectivesAllowBool variables directives
        · simp [collectSelection, ha, GroupsNonempty]
        · cases ht : condition.all (doesFragmentTypeApplyBool schema parentType source)
          · simp [collectSelection, ha, ht, GroupsNonempty]
          · cases hd : activeDefer? variables directives with
            | none =>
                simpa [collectSelection, ha, ht, hd]
                  using collectFields_nonempty schema variables parentType source children
                    usage state
            | some label =>
                simpa [collectSelection, ha, ht, hd, freshExecutionKey]
                  using collectFields_nonempty schema variables parentType source children
                    (some
                      {
                        key := state
                        label := label
                        ancestors :=
                          (usage.map (fun parent => parent.key :: parent.ancestors)).getD
                            []
                      })
                    (state + 1)
  termination_by sizeOf selection

  theorem collectFields_nonempty (schema : Schema) (variables : VariableValues)
      (parentType : Name) (source : ResolverValue ObjectRef) (selections : List Selection)
      (usage : Option DeferUsage) (state : Nat)
      : GroupsNonempty
          ((collectFields schema variables parentType source selections usage).run
            state).1.fields := by
    cases selections with
    | nil => simp [collectFields, GroupsNonempty]
    | cons selection rest =>
        simp only [collectFields, run_bind, StateT.run_pure, id_pure_eq, FieldCollection.append]
        exact groupsNonempty_merge _ _
          (collectSelection_nonempty schema variables parentType source selection usage state)
          (collectFields_nonempty schema variables parentType source rest usage _)
  termination_by sizeOf selections
end

theorem collectSubfields_nonempty (schema : Schema) (variables : VariableValues)
    (parentType : Name) (source : ResolverValue ObjectRef) (fields : List ExecutableField)
    (state : Nat)
    : GroupsNonempty
        ((collectSubfields schema variables parentType source fields).run
          state).1.fields := by
  induction fields generalizing state with
  | nil => simp [collectSubfields, GroupsNonempty]
  | cons field rest ih =>
      simp only [collectSubfields, run_bind, StateT.run_pure, id_pure_eq, FieldCollection.append]
      exact groupsNonempty_merge _ _
        (collectFields_nonempty schema variables parentType source field.selectionSet field.deferUsage state)
        (ih _)

theorem buildExecutionPlan_nonempty (groups : CollectedFieldsMap) (parent : List Nat)
    (h : GroupsNonempty groups)
    : GroupsNonempty (buildExecutionPlan groups parent).collectedFieldsMap
      ∧ ∀ partition ∈ (buildExecutionPlan groups parent).newCollectedFieldsMaps,
          GroupsNonempty partition.2 := by
  have hp := buildExecutionPlan_perm groups parent
  constructor
  · intro group hg
    exact h group (hp.mem_iff.mp (List.mem_append_left _ hg))
  · intro partition hp' group hg
    exact h group (hp.mem_iff.mp (List.mem_append_right _ (List.mem_flatMap.mpr ⟨partition, hp', hg⟩)))

end GraphQL.IncrementalDelivery.Semantics
