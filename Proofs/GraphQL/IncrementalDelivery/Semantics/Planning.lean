import Proofs.GraphQL.IncrementalDelivery.Semantics.Erasure
import Proofs.GraphQL.IncrementalDelivery.Semantics.CollectionProperties

/-! Execution planning preserves every collected response-name group exactly once. -/

namespace GraphQL.IncrementalDelivery.Semantics

open GraphQL.IncrementalDelivery.Execution

def executionPlanGroups (plan : ExecutionPlan) : CollectedFieldsMap :=
  plan.collectedFieldsMap ++ plan.newCollectedFieldsMaps.flatMap Prod.snd

theorem addExecutionPartition_perm (usages : List Nat)
    (group : Name × List ExecutableField)
    (partitions : List (List Nat × CollectedFieldsMap))
    : ((addExecutionPartition usages group partitions).flatMap Prod.snd).Perm
        (group :: partitions.flatMap Prod.snd) := by
  induction partitions with
  | nil => simp [addExecutionPartition]
  | cons partition rest ih =>
      rcases partition with ⟨keys, fields⟩
      cases he : deferUsageSetsEquivalent keys usages
      · simp only [addExecutionPartition, he, Bool.false_eq_true, ↓reduceIte,
          List.flatMap_cons]
        exact (ih.append_left fields).trans List.perm_middle
      · simp [addExecutionPartition, he, List.append_assoc]

theorem executionPlanGroups_step (plan : ExecutionPlan)
    (group : Name × List ExecutableField) (parent : List Nat)
    : (executionPlanGroups
        (if deferUsageSetsEquivalent (getFilteredDeferUsageSet group.2) parent then
            { plan with collectedFieldsMap := plan.collectedFieldsMap ++ [group] }
          else
            {
              plan with
                newCollectedFieldsMaps :=
                  addExecutionPartition (getFilteredDeferUsageSet group.2) group
                    plan.newCollectedFieldsMaps
            })).Perm
        (group :: executionPlanGroups plan) := by
  split
  · simp only [executionPlanGroups, List.append_assoc, List.singleton_append]
    exact List.perm_middle
  · exact ((addExecutionPartition_perm _ _ _).append_left plan.collectedFieldsMap).trans
      List.perm_middle

theorem buildExecutionPlan_perm (groups : CollectedFieldsMap) (parent : List Nat)
    : (executionPlanGroups (buildExecutionPlan groups parent)).Perm groups := by
  have aux (initial : ExecutionPlan) :
      (executionPlanGroups
        (groups.foldl (fun plan group =>
          if deferUsageSetsEquivalent (getFilteredDeferUsageSet group.2) parent then
            { plan with collectedFieldsMap := plan.collectedFieldsMap ++ [group] }
          else {
            plan with
              newCollectedFieldsMaps :=
                addExecutionPartition (getFilteredDeferUsageSet group.2) group
                  plan.newCollectedFieldsMaps
          }) initial)).Perm
      (executionPlanGroups initial ++ groups) := by
    induction groups generalizing initial with
    | nil => simp
    | cons group rest ih =>
        simp only [List.foldl_cons]
        refine (ih _).trans ?_
        refine ((executionPlanGroups_step initial group parent).append_right rest).trans
          ?_
        simpa [List.cons_append]
          using (List.perm_middle (a := group) (l₁ := executionPlanGroups initial)
                  (l₂ := rest)).symm
  simpa [buildExecutionPlan, executionPlanGroups] using aux {}

theorem buildExecutionPlan_erasure_perm (groups : CollectedFieldsMap) (parent : List Nat)
    : (eraseGroups (executionPlanGroups (buildExecutionPlan groups parent))).Perm
        (eraseGroups groups) :=
  (buildExecutionPlan_perm groups parent).map eraseGroup

theorem buildExecutionPlan_preserves_property (property : ExecutableField → Prop)
    (groups : CollectedFieldsMap) (parent : List Nat) (h : GroupsSatisfy property groups)
    : GroupsSatisfy property (buildExecutionPlan groups parent).collectedFieldsMap
      ∧ ∀ partition ∈ (buildExecutionPlan groups parent).newCollectedFieldsMaps,
          GroupsSatisfy property partition.2 := by
  have hp := buildExecutionPlan_perm groups parent
  constructor
  · intro group hg
    exact h group (hp.mem_iff.mp (List.mem_append_left _ hg))
  · intro partition hpartition group hg
    apply h group
    apply hp.mem_iff.mp
    apply List.mem_append_right
    exact List.mem_flatMap.mpr ⟨partition, hpartition, hg⟩

end GraphQL.IncrementalDelivery.Semantics
