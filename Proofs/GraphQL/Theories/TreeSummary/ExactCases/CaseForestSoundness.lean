import Proofs.GraphQL.Theories.ConditionTree.ExecutionEquivalence
import Proofs.GraphQL.Theories.ConditionTree.BooleanVariables
import Proofs.GraphQL.Theories.ConditionTree.RuntimeExtraction
import Proofs.GraphQL.Theories.TreeSummary.ExactCases.RuntimeCases
import Proofs.GraphQL.Theories.TreeSummary.ExactCases.CaseForestRuntimeCases
import Proofs.GraphQL.Theories.TreeSummary.ExactCases.ResolvedContext
import Proofs.GraphQL.Theories.TreeSummary.ExactCases.VariableValues
import Proofs.GraphQL.Theories.TreeSummary.Algebra
import Proofs.GraphQL.Theories.TreeSummary.Soundness
import Proofs.GraphQL.Theories.TreeSummary.ExecutionValidity
import GraphQL.Theories.TreeSummary.ExactCases

/-! Soundness of the exact-case-tree summary fold. -/

namespace GraphQL
namespace TreeSummary
namespace ExactCases

open GraphQL.ConditionTree
open GraphQL.ConditionTree.RuntimeExtraction
open GraphQL.AnnotatedExecution
open GraphQL.Execution
open GraphQL.Execution.FieldGroups
open GraphQL.Algorithms.ExecutionUngroupedUncached.Eager
open Internal

universe u v

namespace WithVariablesProof

def CaseForest.summarizeSelectionSetWithPruning (algebra : Algebra) (schema : Schema)
    (parentType : Name) (inheritedBooleanCondition : List BooleanLiteral)
    (selectionSet : List Selection) (variableValues fixedVariableValues : VariableValues)
    : algebra.Summary :=
  CaseForest.summarizeConditionTree algebra schema inheritedBooleanCondition
    (ConditionTree.ofSelectionSetInScopeWithKnownFalsePruning schema parentType
      inheritedBooleanCondition fixedVariableValues selectionSet)
    variableValues fixedVariableValues

def summarizedGroup (algebra : Algebra) (schema : Schema)
    (variableValues : VariableValues) (group : CollectedFieldGroup)
    (fixedVariableValues : VariableValues := variableValues)
    : algebra.Summary :=
  algebra.field group
    (CaseForest.summarizeChildTypes algebra schema group
      (childParentTypes schema group) variableValues fixedVariableValues)

def summarizeCollectedGroups (algebra : Algebra) (schema : Schema)
    (variableValues : VariableValues) (groups : List CollectedFieldGroup)
    (fixedVariableValues : VariableValues := variableValues)
    : algebra.Summary :=
  match groups with
  | [] => algebra.empty
  | group :: rest =>
      algebra.combine
        (summarizedGroup algebra schema variableValues group fixedVariableValues)
        (summarizeCollectedGroups algebra schema variableValues rest fixedVariableValues)

def summarizedChildren (algebra : Algebra) (schema : Schema)
    (variableValues : VariableValues) (group : CollectedFieldGroup)
    (fixedVariableValues : VariableValues := variableValues)
    : algebra.Summary :=
  CaseForest.summarizeChildTypes algebra schema group
    (childParentTypes schema group) variableValues fixedVariableValues

def summarizeCollectedChildren (algebra : Algebra) (schema : Schema)
    (variableValues : VariableValues) (groups : List CollectedFieldGroup)
    (fixedVariableValues : VariableValues := variableValues)
    : algebra.Summary :=
  match groups with
  | [] => algebra.empty
  | group :: rest =>
      algebra.combine
        (summarizedChildren algebra schema variableValues group fixedVariableValues)
        (summarizeCollectedChildren algebra schema variableValues rest
          fixedVariableValues)

def candidateChildGroups (schema : Schema) (variableValues : VariableValues)
    (childParentType childRuntimeType : Name) (group : CollectedFieldGroup)
    (fixedVariableValues : VariableValues := variableValues)
    : List CollectedFieldGroup :=
  let tree :=
    group.childTreeWithKnownFalsePruning schema childParentType fixedVariableValues
  CaseForestRuntimeCase.fieldGroups childParentType group.childInheritedBooleanCondition
    (.ofConditionTree tree) tree.condition.possibleTypes childRuntimeType variableValues

def candidateChildGroupsFor (schema : Schema) (variableValues : VariableValues)
    (childParentType childRuntimeType : Name) (groups : List CollectedFieldGroup)
    (fixedVariableValues : VariableValues := variableValues)
    : List CollectedFieldGroup :=
  groups.flatMap
    (fun group =>
      candidateChildGroups schema variableValues childParentType childRuntimeType group
        fixedVariableValues)

def groupsWithResponseName (responseName : Name) (groups : List CollectedFieldGroup)
    : List CollectedFieldGroup :=
  groups.filter fun group => group.responseName == responseName

def groupsWithoutResponseName (responseName : Name) (groups : List CollectedFieldGroup)
    : List CollectedFieldGroup :=
  groups.filter fun group => !(group.responseName == responseName)

theorem runtimeCaseGroups_permutationEquivalent_of_perm
    (schema : Schema) (parentType executionParentType runtimeType : Name)
    (inheritedBooleanCondition : List BooleanLiteral)
    {selectionSet executionSelectionSet : List Selection}
    (hselectionSet : selectionSet.Perm executionSelectionSet)
    (variableValues : VariableValues) (ref : ObjectRef)
    (hinherited : booleanConditionAllows variableValues inheritedBooleanCondition = true)
    (hpossible : (schema.getPossibleTypes parentType).contains runtimeType = true)
    : let tree :=
        ConditionTree.ofSelectionSetInScope schema parentType
          inheritedBooleanCondition selectionSet
      RuntimeGroupsPermutationEquivalent
        ((CaseForestRuntimeCase.fieldGroups parentType inheritedBooleanCondition
            (.ofConditionTree tree) tree.condition.possibleTypes runtimeType
            variableValues).map
          CollectedFieldGroup.toExecutableGroup)
        (collectFields schema variableValues executionParentType
          (.object runtimeType ref) executionSelectionSet) := by
  let tree := ConditionTree.ofSelectionSetInScope schema parentType
    inheritedBooleanCondition selectionSet
  have hroot : tree.condition = rootCondition schema parentType := by
    unfold tree ConditionTree.ofSelectionSetInScope
    rw [ConditionTree.Tree.insertSelections_condition]
    rfl
  have hcondition : tree.condition.allows variableValues runtimeType = true := by
    rw [hroot]
    simpa [rootCondition, Condition.allows, booleanConditionAllows] using hpossible
  have hmap := CaseForestRuntimeCase.fieldGroupsToExecutable_eq_collectRuntimeFieldGroups
    schema parentType inheritedBooleanCondition tree runtimeType
    variableValues hinherited hcondition
    (ConditionTree.ofSelectionSetInScope_branchesCoherent schema parentType
      inheritedBooleanCondition selectionSet)
    (by
      rw [hroot]
      exact List.contains_iff_mem.mp hpossible)
  change RuntimeGroupsPermutationEquivalent
    ((CaseForestRuntimeCase.fieldGroups parentType inheritedBooleanCondition
        (.ofConditionTree tree) tree.condition.possibleTypes runtimeType
        variableValues).map
      CollectedFieldGroup.toExecutableGroup)
    (collectFields schema variableValues executionParentType
      (.object runtimeType ref) executionSelectionSet)
  rw [hmap]
  exact
    extracted_runtimeGroups_permutationEquivalent_toPermutedSelectionSet
      schema parentType inheritedBooleanCondition hselectionSet variableValues
        executionParentType runtimeType ref hinherited hpossible

theorem runtimeCaseGroups_permutationEquivalent
    (schema : Schema) (parentType executionParentType runtimeType : Name)
    (inheritedBooleanCondition : List BooleanLiteral)
    (selectionSet : List Selection)
    (variableValues : VariableValues) (ref : ObjectRef)
    (hinherited : booleanConditionAllows variableValues inheritedBooleanCondition = true)
    (hpossible : (schema.getPossibleTypes parentType).contains runtimeType = true)
    : let tree :=
        ConditionTree.ofSelectionSetInScope schema parentType
          inheritedBooleanCondition selectionSet
      RuntimeGroupsPermutationEquivalent
        ((CaseForestRuntimeCase.fieldGroups parentType inheritedBooleanCondition
            (.ofConditionTree tree) tree.condition.possibleTypes runtimeType
            variableValues).map
          CollectedFieldGroup.toExecutableGroup)
        (collectFields schema variableValues executionParentType
          (.object runtimeType ref) selectionSet) := by
  exact runtimeCaseGroups_permutationEquivalent_of_perm schema parentType
    executionParentType runtimeType inheritedBooleanCondition (List.Perm.refl _)
    variableValues ref hinherited hpossible

theorem runtimeCaseGroupsWithVariables_permutationEquivalent_of_perm
    (schema : Schema) (parentType executionParentType runtimeType : Name)
    (inheritedBooleanCondition : List BooleanLiteral)
    {selectionSet executionSelectionSet : List Selection}
    (hselectionSet : selectionSet.Perm executionSelectionSet)
    (runtimeValues pruningValues : VariableValues)
    (hmatch : BooleanValuesMatchForPruning runtimeValues pruningValues)
    (ref : ObjectRef)
    (hinherited : booleanConditionAllows runtimeValues inheritedBooleanCondition = true)
    (hpossible : (schema.getPossibleTypes parentType).contains runtimeType = true)
    : let tree :=
        ConditionTree.ofSelectionSetInScopeWithKnownFalsePruning schema parentType
          inheritedBooleanCondition pruningValues selectionSet
      RuntimeGroupsPermutationEquivalent
        ((CaseForestRuntimeCase.fieldGroups parentType inheritedBooleanCondition
            (.ofConditionTree tree) tree.condition.possibleTypes runtimeType
            runtimeValues).map
          CollectedFieldGroup.toExecutableGroup)
        (collectFields schema runtimeValues executionParentType
          (.object runtimeType ref) executionSelectionSet) := by
  let tree := ConditionTree.ofSelectionSetInScopeWithKnownFalsePruning schema parentType
    inheritedBooleanCondition pruningValues selectionSet
  have hroot : tree.condition = rootCondition schema parentType := by
    unfold tree ConditionTree.ofSelectionSetInScopeWithKnownFalsePruning
      ConditionTree.ofSelectionSetInScope
    rw [ConditionTree.Tree.insertSelections_condition]
    rfl
  have hcondition : tree.condition.allows runtimeValues runtimeType = true := by
    rw [hroot]
    simpa [rootCondition, Condition.allows, booleanConditionAllows] using hpossible
  have hmap := CaseForestRuntimeCase.fieldGroupsToExecutable_eq_collectRuntimeFieldGroups
    schema parentType inheritedBooleanCondition tree runtimeType
    runtimeValues hinherited hcondition
    (ConditionTree.ofSelectionSetInScopeWithKnownFalsePruning_branchesCoherent schema parentType
      inheritedBooleanCondition pruningValues selectionSet)
    (by rw [hroot]; exact List.contains_iff_mem.mp hpossible)
  change RuntimeGroupsPermutationEquivalent
    ((CaseForestRuntimeCase.fieldGroups parentType inheritedBooleanCondition
        (.ofConditionTree tree) tree.condition.possibleTypes runtimeType
        runtimeValues).map
      CollectedFieldGroup.toExecutableGroup)
    (collectFields schema runtimeValues executionParentType
      (.object runtimeType ref) executionSelectionSet)
  rw [hmap]
  exact
    ConditionTree.knownFalsePruning_runtimeGroups_permutationEquivalent_toPermutedSelectionSet
      schema parentType inheritedBooleanCondition runtimeValues pruningValues
        hselectionSet hmatch executionParentType runtimeType ref hinherited hpossible

def StaticGroupsValid (variableValues : VariableValues) (runtimeType : Name)
    (groups : List CollectedFieldGroup)
    : Prop :=
  ∀ group,
    group ∈ groups
    -> booleanConditionAllows variableValues group.inheritedBooleanCondition = true
        ∧ group.condition.allows variableValues runtimeType = true
        ∧ group.selections ≠ []
        ∧ ∀ selection,
            selection ∈ group.selections
            -> ∃ field : Field, selection = field.toSelection group.responseName

theorem runtimeCaseGroups_valid
    (parentType : Name) (inheritedBooleanCondition : List BooleanLiteral)
    (tree : CaseForest) (possibleTypes : PossibleTypeRegion)
    (runtimeType : Name) (variableValues : VariableValues)
    (hinherited : booleanConditionAllows variableValues inheritedBooleanCondition = true)
    (hruntime : runtimeType ∈ possibleTypes)
    : StaticGroupsValid variableValues runtimeType
        (CaseForestRuntimeCase.fieldGroups parentType inheritedBooleanCondition tree
          possibleTypes runtimeType variableValues) := by
  intro group hgroup
  have hconditions := CaseForestRuntimeCase.fieldGroups_conditions parentType
    inheritedBooleanCondition tree possibleTypes runtimeType variableValues hinherited
    hruntime group hgroup
  have hshape := CaseForestRuntimeCase.fieldGroups_shape parentType inheritedBooleanCondition tree
    possibleTypes runtimeType variableValues group hgroup
  exact ⟨hconditions.1, hconditions.2, hshape.1, hshape.2⟩

theorem StaticGroupsValid.filter
    {variableValues : VariableValues} {runtimeType : Name}
    {groups : List CollectedFieldGroup}
    (hvalid : StaticGroupsValid variableValues runtimeType groups)
    (keep : CollectedFieldGroup -> Bool)
    : StaticGroupsValid variableValues runtimeType (groups.filter keep) := by
  intro group hgroup
  exact hvalid group (List.mem_filter.mp hgroup).1

private theorem mappedGroupKeys (groups : List CollectedFieldGroup)
    : (groups.map CollectedFieldGroup.toExecutableGroup).map Prod.fst
      = groups.map CollectedFieldGroup.responseName := by
  simp [List.map_map, CollectedFieldGroup.toExecutableGroup]

theorem staticResponseNamesNodup
    (groups : List CollectedFieldGroup)
    (executionGroups : List (Name × List ExecutableField))
    (hequivalent
      : RuntimeGroupsPermutationEquivalent
          (groups.map CollectedFieldGroup.toExecutableGroup)
          executionGroups)
    : (groups.map CollectedFieldGroup.responseName).Nodup := by
  rw [← mappedGroupKeys groups]
  exact hequivalent.leftKeysNodup

theorem runtimeGroupsPermutationEquivalent_symm
    {left right : List (Name × List ExecutableField)}
    (equivalent : RuntimeGroupsPermutationEquivalent left right)
    : RuntimeGroupsPermutationEquivalent right left := by
  exact {
    leftWellFormed := equivalent.rightWellFormed
    rightWellFormed := equivalent.leftWellFormed
    leftKeysNodup := equivalent.rightKeysNodup
    rightKeysNodup := equivalent.leftKeysNodup
    fieldsPerm := equivalent.fieldsPerm.symm
  }

theorem runtimeGroupsPermutationEquivalent_permuteLeft
    {left reordered right : List (Name × List ExecutableField)}
    (equivalent : RuntimeGroupsPermutationEquivalent left right)
    (hperm : left.Perm reordered)
    : RuntimeGroupsPermutationEquivalent reordered right :=
  runtimeGroupsPermutationEquivalent_symm
    ((runtimeGroupsPermutationEquivalent_symm equivalent).permuteRight hperm)

theorem StaticGroupsValid.perm
    {variableValues : VariableValues} {runtimeType : Name}
    {left right : List CollectedFieldGroup}
    (hvalid : StaticGroupsValid variableValues runtimeType left)
    (hperm : left.Perm right)
    : StaticGroupsValid variableValues runtimeType right := by
  intro group hgroup
  exact hvalid group (hperm.mem_iff.mpr hgroup)

theorem summarizeCollectedGroups_perm
    (algebra : Algebra.{v}) (lawful : algebra.Lawful)
    (schema : Schema) (variableValues : VariableValues)
    (fixedVariableValues : VariableValues)
    {left right : List CollectedFieldGroup} (hperm : left.Perm right)
    : summarizeCollectedGroups algebra schema variableValues left fixedVariableValues
      = summarizeCollectedGroups algebra schema variableValues right
          fixedVariableValues := by
  induction hperm with
  | nil => rfl
  | cons group _ ih =>
      simp only [summarizeCollectedGroups]
      rw [ih]
  | swap left right rest =>
      simp only [summarizeCollectedGroups]
      calc
        algebra.combine
              (summarizedGroup algebra schema variableValues right fixedVariableValues)
              (algebra.combine
                (summarizedGroup algebra schema variableValues left fixedVariableValues)
                (summarizeCollectedGroups algebra schema variableValues rest
                  fixedVariableValues))
            = algebra.combine
                (algebra.combine
                  (summarizedGroup algebra schema variableValues right
                    fixedVariableValues)
                  (summarizedGroup algebra schema variableValues left
                    fixedVariableValues))
                (summarizeCollectedGroups algebra schema variableValues rest
                  fixedVariableValues) :=
          (lawful.combine_assoc _ _ _).symm
        _ = algebra.combine
              (algebra.combine
                (summarizedGroup algebra schema variableValues left fixedVariableValues)
                (summarizedGroup algebra schema variableValues right fixedVariableValues))
              (summarizeCollectedGroups algebra schema variableValues rest
                fixedVariableValues) := by
          rw [lawful.combine_comm
            (summarizedGroup algebra schema variableValues right
              fixedVariableValues)]
        _ = algebra.combine
              (summarizedGroup algebra schema variableValues left fixedVariableValues)
              (algebra.combine
                (summarizedGroup algebra schema variableValues right fixedVariableValues)
                (summarizeCollectedGroups algebra schema variableValues rest
                  fixedVariableValues)) :=
          lawful.combine_assoc _ _ _
  | trans _ _ ihLeft ihRight => exact ihLeft.trans ihRight

theorem alignStaticGroup
    (responseName : Name)
    (executionFields : List ExecutableField)
    (executionTail : List (Name × List ExecutableField))
    (groups : List CollectedFieldGroup)
    (hequivalent
      : RuntimeGroupsPermutationEquivalent
          (groups.map CollectedFieldGroup.toExecutableGroup)
          ((responseName, executionFields) :: executionTail))
    : ∃ group staticTail,
        groups.Perm (group :: staticTail)
        ∧ group.responseName = responseName
        ∧ group.toExecutableGroup.2.Perm executionFields
        ∧ RuntimeGroupsPermutationEquivalent
            (staticTail.map CollectedFieldGroup.toExecutableGroup)
            executionTail := by
  have hright : responseName ∈ (((responseName, executionFields) :: executionTail).map
      Prod.fst) := by simp
  have hleft := (hequivalent.keys responseName).mpr hright
  rw [mappedGroupKeys groups] at hleft
  rcases List.mem_map.mp hleft with ⟨group, hgroup, hname⟩
  rcases List.mem_iff_append.mp hgroup with ⟨before, after, hgroups⟩
  subst groups
  let staticTail := before ++ after
  have hperm :
      (before ++ group :: after).Perm (group :: staticTail) := by
    simp [staticTail]
  have hmappedPerm := hperm.map CollectedFieldGroup.toExecutableGroup
  have haligned :=
    runtimeGroupsPermutationEquivalent_permuteLeft hequivalent hmappedPerm
  have hgroupName : group.responseName = responseName := hname
  have haligned' : RuntimeGroupsPermutationEquivalent
      ((responseName, group.toExecutableGroup.2)
        :: staticTail.map CollectedFieldGroup.toExecutableGroup)
      ((responseName, executionFields) :: executionTail) := by
    simpa [CollectedFieldGroup.toExecutableGroup, hgroupName] using haligned
  exact ⟨group, staticTail, hperm, hgroupName, haligned'.headFields,
    haligned'.tails⟩

theorem summarizeCollectedGroups_eq
    (algebra : Algebra) (schema : Schema) (variableValues : VariableValues)
    (fixedVariableValues : VariableValues)
    (groups : List CollectedFieldGroup)
    : summarizeCollectedGroups algebra schema variableValues groups fixedVariableValues
      = CaseForest.summarizeFieldGroups algebra schema groups variableValues
          fixedVariableValues := by
  induction groups with
  | nil => simp [summarizeCollectedGroups,
      CaseForest.summarizeFieldGroups, combineMap]
  | cons group rest ih =>
      simp only [summarizeCollectedGroups,
        CaseForest.summarizeFieldGroups, combineMap, summarizedGroup]
      simpa [summarizedGroup, CaseForest.summarizeFieldGroups, combineMap] using
        congrArg
          (algebra.combine
            (summarizedGroup algebra schema variableValues group fixedVariableValues))
          ih

theorem summarizeCollectedGroups_append
    (algebra : Algebra.{v}) (lawful : algebra.Lawful)
    (schema : Schema) (variableValues : VariableValues)
    (fixedVariableValues : VariableValues)
    (left right : List CollectedFieldGroup)
    : summarizeCollectedGroups algebra schema variableValues (left ++ right)
        fixedVariableValues
      = algebra.combine
          (summarizeCollectedGroups algebra schema variableValues left
            fixedVariableValues)
          (summarizeCollectedGroups algebra schema variableValues right
            fixedVariableValues) := by
  induction left with
  | nil =>
      simpa [summarizeCollectedGroups] using
        (lawful.empty_combine
          (summarizeCollectedGroups algebra schema variableValues right
            fixedVariableValues)).symm
  | cons group rest ih =>
      simp only [List.cons_append, summarizeCollectedGroups]
      rw [ih, lawful.combine_assoc]

theorem summarizeCollectedChildren_append
    (algebra : Algebra.{v}) (lawful : algebra.Lawful)
    (schema : Schema) (variableValues : VariableValues)
    (fixedVariableValues : VariableValues)
    (left right : List CollectedFieldGroup)
    : summarizeCollectedChildren algebra schema variableValues (left ++ right)
        fixedVariableValues
      = algebra.combine
          (summarizeCollectedChildren algebra schema variableValues left
            fixedVariableValues)
          (summarizeCollectedChildren algebra schema variableValues right
            fixedVariableValues) := by
  induction left with
  | nil =>
      simpa [summarizeCollectedChildren] using
        (lawful.empty_combine
          (summarizeCollectedChildren algebra schema variableValues right
            fixedVariableValues)).symm
  | cons group rest ih =>
      simp only [List.cons_append, summarizeCollectedChildren]
      rw [ih, lawful.combine_assoc]

theorem summarizeCollectedGroups_filter_le
    (algebra : Algebra.{v}) (lawful : algebra.Lawful)
    (schema : Schema) (variableValues : VariableValues)
    (fixedVariableValues : VariableValues)
    (keep : CollectedFieldGroup -> Bool) (groups : List CollectedFieldGroup)
    : lawful.le
        (summarizeCollectedGroups algebra schema variableValues (groups.filter keep)
          fixedVariableValues)
        (summarizeCollectedGroups algebra schema variableValues groups
          fixedVariableValues) := by
  induction groups with
  | nil => exact lawful.le_refl _
  | cons group rest ih =>
      cases hkeep : keep group with
      | false =>
          simp only [List.filter_cons, hkeep, Bool.false_eq_true, if_false,
            summarizeCollectedGroups]
          apply lawful.le_trans _ _ _ ih
          have hadded := lawful.combine_mono algebra.empty
            (summarizedGroup algebra schema variableValues group fixedVariableValues)
            (summarizeCollectedGroups algebra schema variableValues rest
              fixedVariableValues)
            (summarizeCollectedGroups algebra schema variableValues rest
              fixedVariableValues)
            (lawful.empty_le _) (lawful.le_refl _)
          simpa only [lawful.empty_combine] using hadded
      | true =>
          simp only [List.filter_cons, hkeep, if_true, summarizeCollectedGroups]
          exact lawful.combine_right_mono _ ih

theorem summarizeCollectedGroups_partition_responseName
    (algebra : Algebra.{v}) (lawful : algebra.Lawful)
    (schema : Schema) (variableValues : VariableValues)
    (fixedVariableValues : VariableValues)
    (responseName : Name) (groups : List CollectedFieldGroup)
    : summarizeCollectedGroups algebra schema variableValues groups fixedVariableValues
      = algebra.combine
          (summarizeCollectedGroups algebra schema variableValues
            (groupsWithResponseName responseName groups) fixedVariableValues)
          (summarizeCollectedGroups algebra schema variableValues
            (groupsWithoutResponseName responseName groups) fixedVariableValues) := by
  unfold groupsWithResponseName groupsWithoutResponseName
  induction groups with
  | nil => simp [summarizeCollectedGroups, lawful.empty_combine]
  | cons group rest ih =>
      by_cases hname : group.responseName = responseName
      · simp only [List.filter_cons, hname, beq_self_eq_true, Bool.not_true,
          Bool.false_eq_true, if_false, if_true, summarizeCollectedGroups]
        rw [ih]
        exact (lawful.combine_assoc _ _ _).symm
      · have hbeq : (group.responseName == responseName) = false := by simp [hname]
        simp only [List.filter_cons, hbeq, Bool.false_eq_true, if_false,
          Bool.not_false, if_true, summarizeCollectedGroups]
        rw [ih]
        calc
          algebra.combine
                (summarizedGroup algebra schema variableValues group fixedVariableValues)
                (algebra.combine
                  (summarizeCollectedGroups algebra schema variableValues
                    (rest.filter fun candidate => candidate.responseName == responseName)
                    fixedVariableValues)
                  (summarizeCollectedGroups algebra schema variableValues
                    (rest.filter
                      fun candidate => !(candidate.responseName == responseName))
                    fixedVariableValues))
              = algebra.combine
                  (algebra.combine
                    (summarizedGroup algebra schema variableValues group
                      fixedVariableValues)
                    (summarizeCollectedGroups algebra schema variableValues
                      (rest.filter
                        fun candidate =>
                          candidate.responseName == responseName) fixedVariableValues))
                  (summarizeCollectedGroups algebra schema variableValues
                    (rest.filter
                      fun candidate =>
                        !(candidate.responseName == responseName))
                    fixedVariableValues) :=
            (lawful.combine_assoc _ _ _).symm
          _ = algebra.combine
                (algebra.combine
                  (summarizeCollectedGroups algebra schema variableValues
                    (rest.filter
                      fun candidate =>
                        candidate.responseName == responseName) fixedVariableValues)
                  (summarizedGroup algebra schema variableValues group
                    fixedVariableValues))
                (summarizeCollectedGroups algebra schema variableValues
                  (rest.filter
                    fun candidate =>
                      !(candidate.responseName == responseName))
                  fixedVariableValues) := by
            rw [lawful.combine_comm
              (summarizedGroup algebra schema variableValues group
                fixedVariableValues)]
          _ = algebra.combine
                (summarizeCollectedGroups algebra schema variableValues
                  (rest.filter fun candidate => candidate.responseName == responseName)
                  fixedVariableValues)
                (algebra.combine
                  (summarizedGroup algebra schema variableValues group
                    fixedVariableValues)
                  (summarizeCollectedGroups algebra schema variableValues
                    (rest.filter
                      fun candidate =>
                        !(candidate.responseName == responseName))
                    fixedVariableValues)) :=
            lawful.combine_assoc _ _ _

theorem summarizeChildParentType_le
    (algebra : Algebra.{v}) (lawful : algebra.Lawful)
    (schema : Schema) (group : CollectedFieldGroup)
    (parentTypes : TypeNames) (childParentType : Name)
    (hchild : childParentType ∈ parentTypes) (variableValues : VariableValues)
    (fixedVariableValues : VariableValues)
    : lawful.le
        ( let childTree :=
            group.childTreeWithKnownFalsePruning schema childParentType
              fixedVariableValues
          CaseForest.summarize algebra schema group.childInheritedBooleanCondition
            (.ofConditionTree childTree)
            childTree.condition.possibleTypes variableValues fixedVariableValues)
        (CaseForest.summarizeChildTypes algebra schema group parentTypes
          variableValues fixedVariableValues) := by
  cases htypes : parentTypes with
  | nil => simp [htypes] at hchild
  | cons first rest =>
      rw [htypes] at hchild
      cases rest with
      | nil =>
          simp only [List.mem_singleton] at hchild
          subst childParentType
          rw [CaseForest.summarizeChildTypes, joinMap]
          exact lawful.le_refl _
      | cons next tail =>
          rw [CaseForest.summarizeChildTypes, joinMap]
          simp only [List.mem_cons] at hchild
          rcases hchild with rfl | hrest
          · exact lawful.le_join_left _ _
          · apply lawful.le_trans _
              (CaseForest.summarizeChildTypes algebra schema group (next :: tail)
                variableValues fixedVariableValues)
            · exact summarizeChildParentType_le algebra lawful schema group
                (next :: tail) childParentType
                (by simpa only [List.mem_cons] using hrest) variableValues
                fixedVariableValues
            · simpa [CaseForest.summarizeChildTypes, joinMap] using
                (lawful.le_join_right
                  (CaseForest.summarize algebra schema group.childInheritedBooleanCondition
                    (.ofConditionTree
                      (group.childTreeWithKnownFalsePruning schema first fixedVariableValues))
                    (group.childTreeWithKnownFalsePruning schema first
                      fixedVariableValues).condition.possibleTypes
                    variableValues fixedVariableValues)
                  (CaseForest.summarizeChildTypes algebra schema group (next :: tail)
                    variableValues fixedVariableValues))
termination_by sizeOf parentTypes
decreasing_by
  rw [htypes]
  simp_wf
  omega

theorem candidateChildGroupsFor_le_summarizeCollectedChildren
    (algebra : Algebra.{v}) {lawful : algebra.Lawful}
    (schema : Schema) (variableValues : VariableValues)
    (fixedVariableValues : VariableValues)
    (childParentType childRuntimeType : Name)
    (groups : List CollectedFieldGroup)
    (hpossible : childRuntimeType ∈ schema.getPossibleTypes childParentType)
    (hchild : ∀ group, group ∈ groups -> childParentType ∈ childParentTypes schema group)
    : lawful.le
        (summarizeCollectedGroups algebra schema variableValues
          (candidateChildGroupsFor schema variableValues childParentType
            childRuntimeType groups fixedVariableValues) fixedVariableValues)
        (summarizeCollectedChildren algebra schema variableValues groups
          fixedVariableValues) := by
  induction groups with
  | nil => exact lawful.le_refl _
  | cons group rest ih =>
      simp only [candidateChildGroupsFor, List.flatMap_cons,
        summarizeCollectedChildren]
      rw [summarizeCollectedGroups_append algebra lawful schema variableValues
        fixedVariableValues _ _]
      apply lawful.combine_mono
      · unfold candidateChildGroups summarizedChildren
        let childTree :=
          group.childTreeWithKnownFalsePruning schema childParentType fixedVariableValues
        rw [summarizeCollectedGroups_eq algebra schema variableValues
          fixedVariableValues _,
          ← CaseForestRuntimeCase.summarize_eq_resolved algebra schema childParentType
            group.childInheritedBooleanCondition (.ofConditionTree childTree)
            childTree.condition.possibleTypes childRuntimeType variableValues
            fixedVariableValues]
        apply lawful.le_trans _
          (CaseForest.summarize algebra schema group.childInheritedBooleanCondition
            (.ofConditionTree childTree)
            childTree.condition.possibleTypes variableValues fixedVariableValues)
        · apply CaseForestRuntimeCase.summarize_le algebra lawful schema
            childParentType
            group.childInheritedBooleanCondition (.ofConditionTree childTree)
            childTree.condition.possibleTypes childRuntimeType variableValues
            fixedVariableValues
          have hroot : childTree.condition = rootCondition schema childParentType := by
            unfold childTree CollectedFieldGroup.childTreeWithKnownFalsePruning
              ConditionTree.ofSelectionSetInScopeWithKnownFalsePruning
              ConditionTree.ofSelectionSetInScope
            rw [ConditionTree.Tree.insertSelections_condition]
            rfl
          rw [hroot]
          simpa [rootCondition] using hpossible
        · exact summarizeChildParentType_le algebra lawful schema group
            (childParentTypes schema group) childParentType (hchild group (by simp))
            variableValues fixedVariableValues
      · exact ih (by
          intro candidate hcandidate
          exact hchild candidate (by simp [hcandidate]))

theorem representativeMatches_of_mapped_perm
    (group : CollectedFieldGroup)
    (fields : List ExecutableField) (field : ExecutableField)
    (hfields : group.toExecutableGroup.2.Perm fields)
    (hfield : field ∈ fields)
    (hcompatible : ExecutableFieldsFieldValidationMergeCompatible fields)
    : group.representativeMatches field := by
  let representative : ExecutableField :=
    {
      fieldName := group.representativeField.fieldName
      arguments := group.representativeField.arguments
      selectionSet := group.representativeField.selectionSet
    }
  have hrepresentativeMapped : representative ∈ group.toExecutableGroup.2 := by
    unfold CollectedFieldGroup.toExecutableGroup
    apply List.mem_map.mpr
    exact ⟨group.representativeField,
      CollectedFieldGroup.representativeField_mem_fields group, rfl⟩
  have hrepresentative : representative ∈ fields :=
    (hfields.mem_iff).mp hrepresentativeMapped
  simpa [CollectedFieldGroup.representativeMatches, representative] using
    hcompatible representative field hrepresentative hfield

private structure ExecutableFieldAlignment
    (schema : Schema) (variableValues : VariableValues) (runtimeType : Name)
    (group : CollectedFieldGroup) (field : ExecutableField)
    (definition : FieldDefinition)
    : Prop where
  runtimeLookup : schema.lookupField runtimeType field.fieldName = some definition
  parentPossible : runtimeType ∈ group.condition.possibleTypes
  representative : group.representativeMatches field
  argumentsNodup : (field.arguments.map Argument.name).Nodup
  outputType : definition.outputType ∈ group.fieldOutputTypes schema

private theorem executableFieldAlignment
    (schema : Schema) (variableValues : VariableValues) (runtimeType : Name)
    (group : CollectedFieldGroup) (field : ExecutableField)
    (rest : List ExecutableField) (definition : FieldDefinition)
    (hlookup : schema.lookupField runtimeType field.fieldName = some definition)
    (hfields : group.toExecutableGroup.2.Perm (field :: rest))
    (hexecutionValid : ExecutableFieldGroupValid schema runtimeType (field :: rest))
    (hvalid : StaticGroupsValid variableValues runtimeType [group])
    : ExecutableFieldAlignment schema variableValues runtimeType group field
        definition := by
  have hfieldMem : field ∈ group.toExecutableGroup.2 :=
    (hfields.mem_iff).mpr (by simp)
  have hcondition := (hvalid group (by simp)).2.1
  have hparentPossible : runtimeType ∈ group.condition.possibleTypes :=
    List.contains_iff_mem.mp (Bool.and_eq_true_iff.mp hcondition).1
  have hrepresentative := representativeMatches_of_mapped_perm group
    (field :: rest) field hfields (by simp) hexecutionValid.mergeCompatible
  have hlookupRepresentative :
      schema.lookupField runtimeType group.representativeField.fieldName
        = some definition := by
    rw [hrepresentative.1]
    exact hlookup
  exact {
    runtimeLookup := hlookup
    parentPossible := hparentPossible
    representative := hrepresentative
    argumentsNodup := hexecutionValid.argumentsNodup field (by simp)
    outputType :=
      CollectedFieldGroup.representativeOutputType_mem_fieldOutputTypes schema
        variableValues runtimeType group definition hcondition hlookupRepresentative
  }

theorem collectedFieldGroup_mergedSelectionSet_perm
    (group : CollectedFieldGroup)
    (fields : List ExecutableField)
    (_hshape
      : ∀ selection,
          selection ∈ group.selections
          -> ∃ field : Field, selection = field.toSelection group.responseName)
    (hfields : group.toExecutableGroup.2.Perm fields)
    : group.mergedSelectionSet.Perm (Execution.mergedFieldSelectionSet fields) := by
  have hgroup :
      group.mergedSelectionSet
        = Execution.mergedFieldSelectionSet group.toExecutableGroup.2 := by
    rw [CollectedFieldGroup.mergedSelectionSet,
      ConditionTree.FieldGroup.mergedSelectionSet,
      mergedFieldSelectionSet_eq_flatMap]
    simp [
      CollectedFieldGroup.toExecutableGroup, CollectedFieldGroup.fields,
      CollectedFieldGroup.responseName,
      SelectionSet.mergeSelectionSets, ConditionTree.FieldGroup.selections,
      ConditionTree.Field.toSelection,
      Selection.subselections, List.flatMap_map]
  rw [hgroup]
  exact mergedFieldSelectionSet_perm hfields

theorem singleFieldResult_sound_complete
    {concrete : ConcreteAlgebra.{u}} {abstract : Algebra.{v}} {schema : Schema}
    (variableValues fixedVariableValues : VariableValues)
    (parentType responseName : Name)
    (soundness : Soundness concrete abstract schema variableValues)
    (field : ExecutableField) (schemaDefinition : FieldDefinition)
    (completed : Result AnnotatedResponseValue)
    (group : CollectedFieldGroup)
    (hparent : parentType ∈ group.condition.possibleTypes)
    (hrepresentative : group.representativeMatches field)
    (hargumentsNodup : (field.arguments.map Argument.name).Nodup)
    (hlookup : schema.lookupField parentType field.fieldName = some schemaDefinition)
    (houtput : schemaDefinition.outputType ∈ group.fieldOutputTypes schema)
    (hcompleted
      : soundness.approximates
          (foldAnnotatedResponseValueResult concrete completed)
          (foldChildSummaryForValueResult abstract
            (summarizedChildren abstract schema variableValues group fixedVariableValues)
            completed))
    : soundness.approximates
        (foldAnnotatedResponseFieldsResult concrete
          (singleAnnotatedResponseFieldResult schema variableValues schemaDefinition
            parentType responseName field completed))
        (summarizedGroup abstract schema variableValues group fixedVariableValues) := by
  cases completed with
  | error errors => exact soundness.toSoundnessCore.empty_sound_any _
  | ok completed =>
      rcases completed with ⟨value, errors⟩
      have hfield := soundness.field_sound group parentType field schemaDefinition
        value (foldAnnotatedResponseValue concrete value)
        (summarizedChildren abstract schema variableValues group fixedVariableValues)
        hrepresentative hparent hargumentsNodup hlookup houtput hcompleted
      simpa [singleAnnotatedResponseFieldResult,
        resolvedFieldProvenance,
        foldAnnotatedResponseFieldsResult, foldAnnotatedResponseFields,
        summarizedGroup, summarizedChildren,
        soundness.concreteLawful.combine_empty] using hfield

-- The executor follows one exact terminal runtime case. Each recursive object value
-- extracts its own child case; list completion only repeats the same child summary.
private theorem annotatedResponseExecution_related_all
    {concrete : ConcreteAlgebra.{u}} {abstract : Algebra.{v}}
    (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variableValues fixedVariableValues : VariableValues)
    (hpruning : BooleanValuesMatchForPruning variableValues fixedVariableValues)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (soundness : Soundness concrete abstract schema variableValues)
    : (∀ fuel runtimeType source executionGroups,
        ∀ (ref : ObjectRef) staticGroups,
          source = .object runtimeType ref
          -> RuntimeGroupsPermutationEquivalent
              (staticGroups.map CollectedFieldGroup.toExecutableGroup)
              executionGroups
          -> ExecutableGroupsValid schema runtimeType executionGroups
          -> StaticGroupsValid variableValues runtimeType staticGroups
          -> soundness.approximates
              (foldAnnotatedResponseFieldsResult concrete
                (executeQueryAnnotatedCollectedFields schema resolvers variableValues fuel
                  runtimeType source executionGroups))
              (summarizeCollectedGroups abstract schema variableValues staticGroups
                fixedVariableValues))
      ∧ (∀ fuel runtimeType source responseName fields,
          ∀ (ref : ObjectRef) group,
            source = .object runtimeType ref
            -> group.responseName = responseName
            -> group.toExecutableGroup.2.Perm fields
            -> ExecutableFieldGroupValid schema runtimeType fields
            -> StaticGroupsValid variableValues runtimeType [group]
            -> soundness.approximates
                (foldAnnotatedResponseFieldsResult concrete
                  (executeQueryAnnotatedField schema resolvers variableValues fuel
                    runtimeType source responseName fields))
                (summarizedGroup abstract schema variableValues group
                  fixedVariableValues))
      ∧ (∀ fuel fieldType fields value,
          ∀ runtimeType (_ref : ObjectRef) fieldName definition group,
            fieldType.namedType = definition.outputType.namedType
            -> schema.lookupField runtimeType fieldName = some definition
            -> definition.outputType ∈ group.fieldOutputTypes schema
            -> (∃ field, field ∈ fields ∧ field.fieldName = fieldName)
            -> ExecutableFieldGroupValid schema runtimeType fields
            -> group.toExecutableGroup.2.Perm fields
            -> StaticGroupsValid variableValues runtimeType [group]
            -> soundness.approximates
                (foldAnnotatedResponseValueResult concrete
                  (completeAnnotatedResponseValue schema resolvers variableValues fuel
                    fieldType fields value))
                (foldChildSummaryForValueResult abstract
                  (summarizedChildren abstract schema variableValues group
                    fixedVariableValues)
                  (completeAnnotatedResponseValue schema resolvers variableValues fuel
                    fieldType fields value)))
      ∧ (∀ fuel itemType fields values,
          ∀ runtimeType (_ref : ObjectRef) fieldName definition group,
            itemType.namedType = definition.outputType.namedType
            -> schema.lookupField runtimeType fieldName = some definition
            -> definition.outputType ∈ group.fieldOutputTypes schema
            -> (∃ field, field ∈ fields ∧ field.fieldName = fieldName)
            -> ExecutableFieldGroupValid schema runtimeType fields
            -> group.toExecutableGroup.2.Perm fields
            -> StaticGroupsValid variableValues runtimeType [group]
            -> soundness.approximates
                (foldAnnotatedResponseValuesResult concrete
                  (completeAnnotatedResponseValueList schema resolvers variableValues fuel
                    itemType fields values))
                (foldChildSummaryForValuesResult abstract
                  (summarizedChildren abstract schema variableValues group
                    fixedVariableValues)
                  (completeAnnotatedResponseValueList schema resolvers variableValues
                    fuel itemType fields values))) := by
  apply executeQueryAnnotatedCollectedFields.mutual_induct schema resolvers variableValues
  case case1 =>
    intro fuel runtimeType source ref staticGroups _hsource _hequivalent
      _hexecutionValid _hvalid
    simpa [executeQueryAnnotatedCollectedFields,
      foldAnnotatedResponseFieldsResult, foldAnnotatedResponseFields] using
      soundness.toSoundnessCore.empty_sound_any
        (summarizeCollectedGroups abstract schema variableValues staticGroups
          fixedVariableValues)
  case case2 =>
    intro fuel runtimeType source responseName fields rest field_ih tail_ih ref
      staticGroups hsource hequivalent hexecutionValid hvalid
    subst source
    rcases alignStaticGroup responseName fields rest staticGroups hequivalent
      with ⟨group, staticTail, hperm, hname, hfields, htailEquivalent⟩
    have hvalid' := hvalid.perm hperm
    have hgroupExecutionValid := hexecutionValid responseName fields (by simp)
    have hhead := field_ih ref group rfl hname hfields
      hgroupExecutionValid (by
      intro candidate hcandidate
      have heq : candidate = group := List.mem_singleton.mp hcandidate
      subst candidate
      exact hvalid' group (by simp))
    have htail := tail_ih ref staticTail rfl htailEquivalent (by
      intro tailResponseName tailFields htailGroup
      exact hexecutionValid tailResponseName tailFields (by simp [htailGroup])) (by
      intro candidate hcandidate
      exact hvalid' candidate (by simp [hcandidate]))
    have hcombine := soundness.toSoundnessCore.combineFieldsResult_sound _ _ _ _ hhead htail
    rw [executeQueryAnnotatedCollectedFields]
    rw [summarizeCollectedGroups_perm abstract soundness.abstractLawful schema
      variableValues fixedVariableValues hperm]
    exact hcombine
  case case3 =>
    intro fuel runtimeType source responseName ref group _hsource _hname hfields
      _hexecutionValid hvalid
    have hnonempty := (hvalid group (by simp)).2.2.1
    have hmappedNonempty : group.toExecutableGroup.2 ≠ [] := by
      intro hempty
      unfold CollectedFieldGroup.toExecutableGroup at hempty
      dsimp only [Prod.snd] at hempty
      have hfields : group.fields = [] := List.map_eq_nil_iff.mp hempty
      unfold CollectedFieldGroup.fields at hfields
      exact hnonempty (by
        simp [CollectedFieldGroup.selections, ConditionTree.FieldGroup.selections,
          hfields])
    exact False.elim (hmappedNonempty (List.Perm.eq_nil hfields))
  case case4 =>
    intro runtimeType source responseName field rest ref group _hsource _hname _hfields
      _hexecutionValid _hvalid
    simpa [executeQueryAnnotatedField, foldAnnotatedResponseFieldsResult] using
      soundness.toSoundnessCore.empty_sound_any
        (summarizedGroup abstract schema variableValues group fixedVariableValues)
  case case5 =>
    intro runtimeType source responseName field rest fuel hlookup ref group _hsource
      _hname _hfields _hexecutionValid _hvalid
    simpa [executeQueryAnnotatedField, hlookup,
      foldAnnotatedResponseFieldsResult] using
      soundness.toSoundnessCore.empty_sound_any
        (summarizedGroup abstract schema variableValues group fixedVariableValues)
  case case6 =>
    intro runtimeType source responseName field rest fuel definition hlookup hcoerce ref
      group hsource hname hfields hexecutionValid hvalid
    subst source
    have halignment := executableFieldAlignment schema variableValues runtimeType group
      field rest definition hlookup hfields hexecutionValid hvalid
    let completed : Result AnnotatedResponseValue :=
      match definition.outputType with
      | .nonNull _inner => .error 1
      | _ => .ok (.null, 1)
    have hcompleted : soundness.approximates
        (foldAnnotatedResponseValueResult concrete completed)
        (foldChildSummaryForValueResult abstract
          (summarizedChildren abstract schema variableValues group
            fixedVariableValues) completed) := by
      cases htype : definition.outputType <;>
        simp [completed, htype, foldAnnotatedResponseValueResult,
          foldAnnotatedResponseValue, foldChildSummaryForValueResult,
          foldChildSummaryForValue] <;>
        exact soundness.toSoundnessCore.empty_sound_any _
    have hsingle := singleFieldResult_sound_complete variableValues
      fixedVariableValues runtimeType responseName soundness field definition completed
      group halignment.parentPossible halignment.representative
      halignment.argumentsNodup hlookup halignment.outputType hcompleted
    simp only [executeQueryAnnotatedField, hlookup]
    rw [hcoerce]
    exact hsingle
  case case7 =>
    intro runtimeType source responseName field rest fuel definition hlookup
      coercedArguments hcoerce hresolve ref group hsource hname hfields hexecutionValid hvalid
    subst source
    have halignment := executableFieldAlignment schema variableValues runtimeType group
      field rest definition hlookup hfields hexecutionValid hvalid
    let completed : Result AnnotatedResponseValue :=
      match definition.outputType with
      | .nonNull _inner => .error 1
      | _ => .ok (.null, 1)
    have hcompleted : soundness.approximates
        (foldAnnotatedResponseValueResult concrete completed)
        (foldChildSummaryForValueResult abstract
          (summarizedChildren abstract schema variableValues group
            fixedVariableValues) completed) := by
      cases htype : definition.outputType <;>
        simp [completed, htype, foldAnnotatedResponseValueResult,
          foldAnnotatedResponseValue, foldChildSummaryForValueResult,
          foldChildSummaryForValue] <;>
        exact soundness.toSoundnessCore.empty_sound_any _
    have hsingle := singleFieldResult_sound_complete variableValues
      fixedVariableValues runtimeType responseName soundness field definition completed
      group halignment.parentPossible halignment.representative
      halignment.argumentsNodup hlookup halignment.outputType hcompleted
    simp only [executeQueryAnnotatedField, hlookup, hcoerce]
    rw [hresolve]
    exact hsingle
  case case8 =>
    intro runtimeType source responseName field rest fuel definition hlookup
      coercedArguments hcoerce resolved hresolve complete_ih ref group hsource hname hfields
      hexecutionValid hvalid
    subst source
    have halignment := executableFieldAlignment schema variableValues runtimeType group
      field rest definition hlookup hfields hexecutionValid hvalid
    have hcompleted := complete_ih runtimeType ref field.fieldName definition
      group rfl halignment.runtimeLookup halignment.outputType ⟨field, by simp, rfl⟩
      hexecutionValid hfields hvalid
    have hsingle := singleFieldResult_sound_complete variableValues
      fixedVariableValues runtimeType responseName soundness field definition
      (completeAnnotatedResponseValue schema resolvers variableValues fuel
        definition.outputType (field :: rest) resolved)
      group halignment.parentPossible halignment.representative
      halignment.argumentsNodup hlookup halignment.outputType hcompleted
    simpa [executeQueryAnnotatedField, hlookup, hcoerce, hresolve] using hsingle
  case case9 =>
    intro fieldType fields value runtimeType ref fieldName definition group
      _hnamed _hlookup _houtput _hwitness _hexecutionValid _hfields _hvalid
    simpa [completeAnnotatedResponseValue, foldAnnotatedResponseValueResult,
      foldChildSummaryForValueResult] using
      soundness.empty_sound
  case case10 =>
    intro fuel inner fields value hfuel complete_ih runtimeType ref fieldName
      definition group hnamed hlookup houtput hwitness hexecutionValid hfields hvalid
    have hinner := complete_ih runtimeType ref fieldName definition group
      (by simpa [TypeRef.namedType] using hnamed) hlookup houtput hwitness
      hexecutionValid hfields hvalid
    simpa [completeAnnotatedResponseValue, hfuel] using
      soundness.toSoundnessCore.completeNonNullResult_sound
        (completeAnnotatedResponseValue schema resolvers variableValues fuel inner fields
          value)
        (summarizedChildren abstract schema variableValues group fixedVariableValues)
        hinner
  case case11 =>
    intro fuel fieldType fields hnotNonNull runtimeType ref fieldName
      definition group _hnamed _hlookup _houtput _hwitness _hexecutionValid
      _hfields _hvalid
    simpa [completeAnnotatedResponseValue, hnotNonNull,
      foldAnnotatedResponseValueResult, foldAnnotatedResponseValue,
      foldChildSummaryForValueResult, foldChildSummaryForValue] using
      soundness.empty_sound
  case case12 =>
    intro fuel typeName fields value hcomposite runtimeType ref fieldName
      definition group _hnamed _hlookup _houtput _hwitness _hexecutionValid
      _hfields _hvalid
    simpa [completeAnnotatedResponseValue, hcomposite,
      foldAnnotatedResponseValueResult, foldChildSummaryForValueResult] using
      soundness.empty_sound
  case case13 =>
    intro fuel typeName fields value hnotComposite runtimeType ref fieldName
      definition group _hnamed _hlookup _houtput _hwitness _hexecutionValid
      _hfields _hvalid
    have hcomposite : (TypeRef.named typeName).isCompositeBool schema = false := by
      cases hvalue : (TypeRef.named typeName).isCompositeBool schema with
      | false => rfl
      | true => exact False.elim (hnotComposite hvalue)
    simpa [completeAnnotatedResponseValue, hcomposite,
      foldAnnotatedResponseValueResult, foldAnnotatedResponseValue,
      foldChildSummaryForValueResult, foldChildSummaryForValue] using
      soundness.empty_sound
  case case14 =>
    intro fuel childParentType fields childRuntimeType childRef hinclude childGroups
      child_ih runtimeType ref fieldName definition group hnamed hlookup
      houtput hwitness hexecutionValid hfields hvalid
    have hchildParent : childParentType = definition.outputType.namedType := by
      simpa [TypeRef.namedType] using hnamed
    subst childParentType
    let childStaticGroups := candidateChildGroups schema variableValues
      definition.outputType.namedType childRuntimeType group fixedVariableValues
    have hpossible :
        (schema.getPossibleTypes definition.outputType.namedType).contains childRuntimeType
          = true := by
      simpa [Schema.typeIncludesObjectBool] using hinclude
    have hselectionPerm : group.mergedSelectionSet.Perm
        (Execution.mergedFieldSelectionSet fields) :=
      collectedFieldGroup_mergedSelectionSet_perm group fields
        (hvalid group (by simp)).2.2.2 hfields
    rcases hwitness with ⟨first, hfirst, hfirstName⟩
    have hlookupFirst :
        schema.lookupField runtimeType first.fieldName = some definition := by
      rw [hfirstName]
      exact hlookup
    rcases hexecutionValid.childrenValid first definition childRuntimeType hfirst hlookupFirst
        hinclude with
      ⟨hchildObject, hchildReady, hchildMerge⟩
    have hchildArguments : selectionSetArgumentsNodup
        (Execution.mergedFieldSelectionSet fields) :=
      selectionSetArgumentsNodup_mergedFieldSelectionSet fields
        hexecutionValid.childArgumentsNodup
    have hchildExecutionValid : ExecutableGroupsValid schema childRuntimeType childGroups := by
      have hcollected := collectFields_executableGroupsValid schema variableValues
        childRuntimeType childRef (Execution.mergedFieldSelectionSet fields)
        hschema hchildObject hchildReady hchildMerge hchildArguments
      simpa [childGroups,
        NormalForm.collectSubfields_eq_collectFields_mergedFieldSelectionSet] using
        hcollected
    have hchildInherited : booleanConditionAllows variableValues
        group.childInheritedBooleanCondition = true :=
      ConditionTree.childInheritedBooleanCondition_allows variableValues
        group.inheritedBooleanCondition group.condition.booleanCondition
        (hvalid group (by simp)).1
        (Bool.and_eq_true_iff.mp (hvalid group (by simp)).2.1).2
    have hchildEquivalent : RuntimeGroupsPermutationEquivalent
        (childStaticGroups.map CollectedFieldGroup.toExecutableGroup)
        childGroups := by
      simpa [childStaticGroups, candidateChildGroups, childGroups,
        NormalForm.collectSubfields_eq_collectFields_mergedFieldSelectionSet,
        CollectedFieldGroup.childTreeWithKnownFalsePruning] using
        runtimeCaseGroupsWithVariables_permutationEquivalent_of_perm schema
          definition.outputType.namedType childRuntimeType childRuntimeType
          group.childInheritedBooleanCondition hselectionPerm variableValues
          fixedVariableValues hpruning childRef
          hchildInherited hpossible
    have hchildValid : StaticGroupsValid variableValues childRuntimeType childStaticGroups := by
      unfold childStaticGroups candidateChildGroups
      exact runtimeCaseGroups_valid definition.outputType.namedType
        group.childInheritedBooleanCondition
        (.ofConditionTree
          (group.childTreeWithKnownFalsePruning schema definition.outputType.namedType
            fixedVariableValues))
        (group.childTreeWithKnownFalsePruning schema definition.outputType.namedType
          fixedVariableValues).condition.possibleTypes
        childRuntimeType variableValues hchildInherited
        (by
          have hroot :
              (group.childTreeWithKnownFalsePruning schema definition.outputType.namedType
                fixedVariableValues).condition
                = rootCondition schema definition.outputType.namedType := by
            unfold CollectedFieldGroup.childTreeWithKnownFalsePruning
              ConditionTree.ofSelectionSetInScopeWithKnownFalsePruning
              ConditionTree.ofSelectionSetInScope
            rw [ConditionTree.Tree.insertSelections_condition]
            rfl
          rw [hroot]
          simpa [rootCondition] using List.contains_iff_mem.mp hpossible)
    have hchild := child_ih childRef childStaticGroups rfl
      hchildEquivalent hchildExecutionValid hchildValid
    have hcandidatesLe : soundness.abstractLawful.le
        (summarizeCollectedGroups abstract schema variableValues childStaticGroups
          fixedVariableValues)
        (summarizedChildren abstract schema variableValues group
          fixedVariableValues) := by
      have hchildType : definition.outputType.namedType ∈ childParentTypes schema group := by
        unfold childParentTypes
        simp only [List.mem_eraseDups, List.mem_map]
        exact ⟨definition.outputType, houtput, rfl⟩
      have hbound := candidateChildGroupsFor_le_summarizeCollectedChildren abstract
        (lawful := soundness.abstractLawful) schema variableValues fixedVariableValues
        definition.outputType.namedType childRuntimeType [group]
        (List.contains_iff_mem.mp hpossible)
        (by
          intro candidate hcandidate
          have heq : candidate = group := List.mem_singleton.mp hcandidate
          simpa [heq] using hchildType)
      simpa [candidateChildGroupsFor, childStaticGroups, summarizeCollectedChildren,
        summarizedChildren, soundness.abstractLawful.combine_empty] using hbound
    have hchild' := soundness.approximates_upward _ _ _ hchild hcandidatesLe
    cases hresult : executeQueryAnnotatedCollectedFields schema resolvers variableValues fuel
        childRuntimeType (.object childRuntimeType childRef) childGroups with
    | error errors =>
        have hresult' :
            executeQueryAnnotatedCollectedFields schema resolvers variableValues fuel
                childRuntimeType (.object childRuntimeType childRef)
                (collectFields schema variableValues childRuntimeType
                  (.object childRuntimeType childRef)
                  (Execution.mergedFieldSelectionSet fields))
              = .error errors := by
          simpa [childGroups,
            NormalForm.collectSubfields_eq_collectFields_mergedFieldSelectionSet] using
            hresult
        simpa [completeAnnotatedResponseValue, hinclude, hresult',
          catchAnnotatedResponseBubbleAsNull,
          foldAnnotatedResponseValueResult, foldAnnotatedResponseValue,
          foldChildSummaryForValueResult, foldChildSummaryForValue] using
          soundness.empty_sound
    | ok completed =>
        rcases completed with ⟨childFields, errors⟩
        rw [hresult] at hchild'
        have hresult' :
            executeQueryAnnotatedCollectedFields schema resolvers variableValues fuel
                childRuntimeType (.object childRuntimeType childRef)
                (collectFields schema variableValues childRuntimeType
                  (.object childRuntimeType childRef)
                  (Execution.mergedFieldSelectionSet fields))
              = .ok (childFields, errors) := by
          simpa [childGroups,
            NormalForm.collectSubfields_eq_collectFields_mergedFieldSelectionSet] using
            hresult
        have hchildFields : soundness.approximates
            (foldAnnotatedResponseFields concrete childFields)
            (summarizedChildren abstract schema variableValues group
              fixedVariableValues) := by
          simpa [foldAnnotatedResponseFieldsResult] using hchild'
        simpa [completeAnnotatedResponseValue, hinclude, hresult',
          catchAnnotatedResponseBubbleAsNull,
          foldAnnotatedResponseValueResult, foldAnnotatedResponseValue,
          foldChildSummaryForValueResult, foldChildSummaryForValue,
          soundness.abstractLawful.combine_empty] using hchildFields
  case case15 =>
    intro fuel parentType fields childRuntimeType childRef hnotInclude runtimeType ref
      fieldName definition group _hnamed _hlookup _houtput _hwitness
      _hexecutionValid _hfields _hvalid
    have hinclude : schema.typeIncludesObjectBool parentType childRuntimeType = false := by
      cases hvalue : schema.typeIncludesObjectBool parentType childRuntimeType with
      | false => rfl
      | true => exact False.elim (hnotInclude hvalue)
    simpa [completeAnnotatedResponseValue, hinclude,
      foldAnnotatedResponseValueResult, foldChildSummaryForValueResult] using
      soundness.empty_sound
  case case16 =>
    intro fuel inner fields values list_ih runtimeType ref fieldName
      definition group hnamed hlookup houtput hwitness hexecutionValid hfields hvalid
    have hlist := list_ih runtimeType ref fieldName definition group
      (by simpa [TypeRef.namedType] using hnamed) hlookup houtput hwitness
      hexecutionValid hfields hvalid
    cases hresult : completeAnnotatedResponseValueList schema resolvers variableValues fuel
        inner fields values with
    | error errors =>
        simpa [completeAnnotatedResponseValue, hresult,
          catchAnnotatedResponseBubbleAsNull,
          foldAnnotatedResponseValueResult, foldAnnotatedResponseValue,
          foldChildSummaryForValueResult, foldChildSummaryForValue] using
          soundness.empty_sound
    | ok completed =>
        rcases completed with ⟨completedValues, errors⟩
        rw [hresult] at hlist
        have hvalues : soundness.approximates
            (foldAnnotatedResponseValues concrete completedValues)
            (foldChildSummaryForValues abstract
              (summarizedChildren abstract schema variableValues group
                fixedVariableValues)
              completedValues) := by
          simpa [foldAnnotatedResponseValuesResult,
            foldChildSummaryForValuesResult] using hlist
        simpa [completeAnnotatedResponseValue, hresult,
          catchAnnotatedResponseBubbleAsNull,
          foldAnnotatedResponseValueResult, foldAnnotatedResponseValue,
          foldChildSummaryForValueResult, foldChildSummaryForValue] using hvalues
  case case17 =>
    intro fuel typeName fields values runtimeType ref fieldName definition
      group _hnamed _hlookup _houtput _hwitness _hexecutionValid _hfields
      _hvalid
    simpa [completeAnnotatedResponseValue, foldAnnotatedResponseValueResult,
      foldChildSummaryForValueResult] using
      soundness.empty_sound
  case case18 =>
    intro fuel inner fields value hnotNull hnotList runtimeType ref fieldName
      definition group _hnamed _hlookup _houtput _hwitness _hexecutionValid
      _hfields _hvalid
    simpa [completeAnnotatedResponseValue, hnotNull, hnotList,
      foldAnnotatedResponseValueResult, foldChildSummaryForValueResult] using
      soundness.empty_sound
  case case19 =>
    intro fuel itemType fields runtimeType ref fieldName definition group
      _hnamed _hlookup _houtput _hwitness _hexecutionValid _hfields _hvalid
    simpa [completeAnnotatedResponseValueList,
      foldAnnotatedResponseValuesResult, foldAnnotatedResponseValues,
      foldChildSummaryForValuesResult, foldChildSummaryForValues] using
      soundness.empty_sound
  case case20 =>
    intro fuel itemType fields value values head_ih tail_ih runtimeType ref
      fieldName definition group hnamed hlookup houtput hwitness hexecutionValid
      hfields hvalid
    have hhead := head_ih runtimeType ref fieldName definition group hnamed
      hlookup houtput hwitness hexecutionValid hfields hvalid
    have htail := tail_ih runtimeType ref fieldName definition group hnamed
      hlookup houtput hwitness hexecutionValid hfields hvalid
    simpa [completeAnnotatedResponseValueList] using
      soundness.toSoundnessCore.combineValuesResult_sound
        (completeAnnotatedResponseValue schema resolvers variableValues fuel itemType fields
          value)
        (completeAnnotatedResponseValueList schema resolvers variableValues fuel itemType
          fields values)
        (summarizedChildren abstract schema variableValues group fixedVariableValues)
        hhead htail

theorem Soundness.executeQueryAnnotatedWithFuel_soundAt
    {concrete : ConcreteAlgebra.{u}} {abstract : Algebra.{v}} {schema : Schema}
    (operation : Operation) (resolvers : Resolvers ObjectRef)
    (variableValues : VariableValues)
    (pruningValues : VariableValues)
    (hmatch
      : BooleanValuesMatchForPruning
          (coerceVariableValues operation variableValues) pruningValues)
    (soundness
      : Soundness concrete abstract schema
          (coerceVariableValues operation variableValues))
    (fuel : Nat)
    (source : ResolverValue ObjectRef)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (hoperation : Validation.operationDefinitionValid schema operation)
    : soundness.approximates
        (foldAnnotatedResponse concrete
          (executeQueryAnnotatedWithFuel schema resolvers variableValues operation fuel
            source))
        (CaseForest.summarizeSelectionSetWithPruning abstract schema
          (operation.rootType schema) []
          operation.selectionSet (coerceVariableValues operation variableValues)
          pruningValues) := by
  have hrootObject : schema.objectType (operation.rootType schema) := by
    rw [Validation.operationDefinitionValid_rootType_eq hoperation]
    exact hschema.2.1
  let coercedVariableValues := coerceVariableValues operation variableValues
  cases hroot : rootSourceAppliesBool schema operation source with
  | false =>
      simpa [executeQueryAnnotatedWithFuel, hroot, foldAnnotatedResponse,
        foldAnnotatedResponseValue] using
        soundness.toSoundnessCore.empty_sound_any
          (CaseForest.summarizeSelectionSetWithPruning abstract schema
            (operation.rootType schema) []
            operation.selectionSet (coerceVariableValues operation variableValues)
            pruningValues)
  | true =>
      obtain ⟨runtimeType, ref, rfl, hinclude⟩ :=
        NormalForm.GroundTypeNormalization.rootSourceAppliesBool_true_object
          schema operation source hroot
      have hruntimeType : runtimeType = operation.rootType schema :=
        object_typeIncludesObjectBool_eq_self schema hrootObject hinclude
      subst runtimeType
      let tree := ConditionTree.ofSelectionSetInScopeWithKnownFalsePruning schema
        (operation.rootType schema) [] pruningValues operation.selectionSet
      let staticGroups := CaseForestRuntimeCase.fieldGroups (operation.rootType schema) []
        (.ofConditionTree tree) tree.condition.possibleTypes
        (operation.rootType schema) coercedVariableValues
      let executionGroups := collectFields schema coercedVariableValues
        (operation.rootType schema) (.object (operation.rootType schema) ref)
        operation.selectionSet
      have hpossible :
          (schema.getPossibleTypes (operation.rootType schema)).contains
              (operation.rootType schema) = true := by
        simpa [Schema.typeIncludesObjectBool] using hinclude
      have hrootCondition : tree.condition = rootCondition schema
          (operation.rootType schema) := by
        unfold tree
          ConditionTree.ofSelectionSetInScopeWithKnownFalsePruning
          ConditionTree.ofSelectionSetInScope
        rw [ConditionTree.Tree.insertSelections_condition]
        rfl
      have htreePossible : operation.rootType schema ∈ tree.condition.possibleTypes := by
        rw [hrootCondition]
        simpa [rootCondition] using List.contains_iff_mem.mp hpossible
      have hequivalent : RuntimeGroupsPermutationEquivalent
          (staticGroups.map CollectedFieldGroup.toExecutableGroup)
          executionGroups := by
        simpa [tree, staticGroups, executionGroups] using
          runtimeCaseGroupsWithVariables_permutationEquivalent_of_perm schema
            (operation.rootType schema) (operation.rootType schema)
            (operation.rootType schema) [] (List.Perm.refl operation.selectionSet)
            coercedVariableValues pruningValues hmatch ref
            (by simp [booleanConditionAllows]) hpossible
      have hvalid : StaticGroupsValid coercedVariableValues
          (operation.rootType schema) staticGroups := by
        exact runtimeCaseGroups_valid (operation.rootType schema) []
          (.ofConditionTree tree) tree.condition.possibleTypes
          (operation.rootType schema) coercedVariableValues
          (by simp [booleanConditionAllows]) htreePossible
      have hexecutionValid : ExecutableGroupsValid schema (operation.rootType schema)
          executionGroups := by
        have hready :=
          NormalForm.selectionSetSemanticsReady_of_selectionSetValid_object schema
            operation.variableDefinitions (operation.rootType schema) hschema hrootObject
            operation.selectionSet
            (Validation.operationDefinitionValid_selectionSetValid hoperation)
        have harguments := Execution.selectionSetArgumentsNodup_of_selectionSetValid
          (Validation.operationDefinitionValid_selectionSetValid hoperation)
        exact collectFields_executableGroupsValid schema coercedVariableValues
          (operation.rootType schema) ref operation.selectionSet hschema hrootObject hready
          (Validation.operationDefinitionValid_fieldsInSetCanMerge hoperation) harguments
      have hrelated :=
        (annotatedResponseExecution_related_all schema resolvers coercedVariableValues
          pruningValues hmatch hschema soundness).1 fuel (operation.rootType schema)
          (.object (operation.rootType schema) ref) executionGroups ref staticGroups
          rfl hequivalent hexecutionValid hvalid
      have hsummaryLe : soundness.abstractLawful.le
          (summarizeCollectedGroups abstract schema coercedVariableValues staticGroups
            pruningValues)
          (CaseForest.summarizeSelectionSetWithPruning abstract schema
            (operation.rootType schema) []
            operation.selectionSet coercedVariableValues pruningValues) := by
        rw [summarizeCollectedGroups_eq abstract schema coercedVariableValues
          pruningValues _]
        rw [← CaseForestRuntimeCase.summarize_eq_resolved abstract schema
          (operation.rootType schema) [] (.ofConditionTree tree)
          tree.condition.possibleTypes (operation.rootType schema)
          coercedVariableValues pruningValues]
        exact CaseForestRuntimeCase.summarize_le abstract soundness.abstractLawful schema
          (operation.rootType schema) [] (.ofConditionTree tree)
          tree.condition.possibleTypes (operation.rootType schema)
          coercedVariableValues pruningValues htreePossible
      have hrelated' := soundness.approximates_upward _ _ _ hrelated hsummaryLe
      cases hresult
            : executeQueryAnnotatedCollectedFields schema resolvers
                coercedVariableValues fuel (operation.rootType schema)
                (.object (operation.rootType schema) ref) executionGroups with
      | error errors =>
          rw [hresult] at hrelated'
          simpa [executeQueryAnnotatedWithFuel, hroot, coercedVariableValues,
            executionGroups, hresult, foldAnnotatedResponse,
            foldAnnotatedResponseValue,
            foldAnnotatedResponseFieldsResult] using hrelated'
      | ok completed =>
          rcases completed with ⟨fields, errors⟩
          rw [hresult] at hrelated'
          simpa [executeQueryAnnotatedWithFuel, hroot, coercedVariableValues,
            executionGroups, hresult, foldAnnotatedResponse,
            foldAnnotatedResponseValue,
            foldAnnotatedResponseFieldsResult] using hrelated'

-- Proof-facing fuel variant used by analyses whose algebra depends on coerced request
-- variables. The public definition module exposes only the default-executor statement.
def OperationWithVariablesSoundWithFuel
    {concrete : ConcreteAlgebra.{u}}
    (algebraFor : VariableValues -> Algebra.{v}) {schema : Schema}
    (soundnessFor : ∀ values, Soundness concrete (algebraFor values) schema values)
    (operation : Operation)
    : Prop :=
  SchemaWellFormedness.schemaWellFormed schema
  -> Validation.operationDefinitionValid schema operation
  -> ∀ (ObjectRef : Type) (resolvers : Resolvers ObjectRef)
        (variableValues : VariableValues) (fuel : Nat)
        (source : ResolverValue ObjectRef),
      let coercedVariableValues := Execution.coerceVariableValues operation variableValues
      (soundnessFor coercedVariableValues).approximates
        (foldAnnotatedResponse concrete
          (executeQueryAnnotatedWithFuel schema resolvers variableValues operation fuel
            source))
        (summarizeOperationWithVariables algebraFor schema variableValues operation)

theorem operationWithVariablesSoundWithFuel
    {concrete : ConcreteAlgebra.{u}}
    (algebraFor : VariableValues -> Algebra.{v}) {schema : Schema}
    (soundnessFor : ∀ values, Soundness concrete (algebraFor values) schema values)
    (operation : Operation)
    : OperationWithVariablesSoundWithFuel algebraFor soundnessFor operation := by
  intro hschema hoperation ObjectRef resolvers variableValues fuel source
  let coercedVariableValues := coerceVariableValues operation variableValues
  have hrelated :=
    Soundness.executeQueryAnnotatedWithFuel_soundAt operation resolvers
      variableValues
      coercedVariableValues (by intro variableName value hvalue; rw [hvalue]; rfl)
      (soundnessFor coercedVariableValues) fuel source hschema hoperation
  simpa [summarizeOperationWithVariables, CaseForest.summarizeSelectionSet,
    CaseForest.summarizeSelectionSetWithPruning,
    coercedVariableValues] using hrelated

theorem analysisWithVariablesSound
    {concrete : ConcreteAlgebra.{u}}
    (algebraFor : VariableValues -> Algebra.{v}) {schema : Schema}
    (soundnessFor : ∀ values, Soundness concrete (algebraFor values) schema values)
    (operation : Operation)
    : AnalysisWithVariablesSound algebraFor soundnessFor operation := by
  intro hschema hoperation ObjectRef resolvers variableValues source
  have hsound := operationWithVariablesSoundWithFuel algebraFor soundnessFor operation
    hschema hoperation ObjectRef resolvers variableValues
    (executeQueryFuelBound schema operation) source
  simpa [executeQueryAnnotated] using hsound

end WithVariablesProof

end ExactCases
end TreeSummary
end GraphQL
