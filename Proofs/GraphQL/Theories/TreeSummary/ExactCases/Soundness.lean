import Proofs.GraphQL.Theories.ConditionTree.ExecutionEquivalence
import Proofs.GraphQL.Theories.ConditionTree.BooleanVariables
import Proofs.GraphQL.Theories.ConditionTree.RuntimeExtraction
import Proofs.GraphQL.Theories.TreeSummary.ExactCases.RuntimeCases
import Proofs.GraphQL.Theories.TreeSummary.ExactCases.ResolvedContext
import Proofs.GraphQL.Theories.TreeSummary.ExactCases.VariableValues
import Proofs.GraphQL.Theories.TreeSummary.Algebra
import Proofs.GraphQL.Theories.TreeSummary.ResponseFold
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

universe u v

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
  RuntimeCase.fieldGroups childParentType group.childInheritedBooleanCondition
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
        ((RuntimeCase.fieldGroups parentType inheritedBooleanCondition
            (.ofConditionTree tree) tree.condition.possibleTypes runtimeType
            variableValues).map
          (RuntimeCase.collectedFieldGroupToExecutableGroup executionParentType))
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
  have hmap := RuntimeCase.fieldGroupsToExecutable_eq_collectRuntimeFieldGroups
    schema parentType executionParentType inheritedBooleanCondition tree runtimeType
    variableValues hinherited hcondition
    (ConditionTree.ofSelectionSetInScope_branchesCoherent schema parentType
      inheritedBooleanCondition selectionSet)
    (by
      rw [hroot]
      exact List.contains_iff_mem.mp hpossible)
  change RuntimeGroupsPermutationEquivalent
    ((RuntimeCase.fieldGroups parentType inheritedBooleanCondition
        (.ofConditionTree tree) tree.condition.possibleTypes runtimeType
        variableValues).map
      (RuntimeCase.collectedFieldGroupToExecutableGroup executionParentType))
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
        ((RuntimeCase.fieldGroups parentType inheritedBooleanCondition
            (.ofConditionTree tree) tree.condition.possibleTypes runtimeType
            variableValues).map
          (RuntimeCase.collectedFieldGroupToExecutableGroup executionParentType))
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
        ((RuntimeCase.fieldGroups parentType inheritedBooleanCondition
            (.ofConditionTree tree) tree.condition.possibleTypes runtimeType
            runtimeValues).map
          (RuntimeCase.collectedFieldGroupToExecutableGroup executionParentType))
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
  have hmap := RuntimeCase.fieldGroupsToExecutable_eq_collectRuntimeFieldGroups
    schema parentType executionParentType inheritedBooleanCondition tree runtimeType
    runtimeValues hinherited hcondition
    (ConditionTree.ofSelectionSetInScopeWithKnownFalsePruning_branchesCoherent schema parentType
      inheritedBooleanCondition pruningValues selectionSet)
    (by rw [hroot]; exact List.contains_iff_mem.mp hpossible)
  change RuntimeGroupsPermutationEquivalent
    ((RuntimeCase.fieldGroups parentType inheritedBooleanCondition
        (.ofConditionTree tree) tree.condition.possibleTypes runtimeType
        runtimeValues).map
      (RuntimeCase.collectedFieldGroupToExecutableGroup executionParentType))
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
        (RuntimeCase.fieldGroups parentType inheritedBooleanCondition tree possibleTypes
          runtimeType variableValues) := by
  intro group hgroup
  have hconditions := RuntimeCase.fieldGroups_conditions parentType
    inheritedBooleanCondition tree possibleTypes runtimeType variableValues hinherited
    hruntime group hgroup
  have hshape := RuntimeCase.fieldGroups_shape parentType inheritedBooleanCondition tree
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

private theorem mappedGroupKeys
    (executionParentType : Name) (groups : List CollectedFieldGroup)
    : (groups.map
        (RuntimeCase.collectedFieldGroupToExecutableGroup executionParentType)).map
        Prod.fst
      = groups.map CollectedFieldGroup.responseName := by
  simp [List.map_map, RuntimeCase.collectedFieldGroupToExecutableGroup]

theorem staticResponseNamesNodup
    (executionParentType : Name) (groups : List CollectedFieldGroup)
    (executionGroups : List (Name × List ExecutableField))
    (hequivalent
      : RuntimeGroupsPermutationEquivalent
          (groups.map
            (RuntimeCase.collectedFieldGroupToExecutableGroup executionParentType))
          executionGroups)
    : (groups.map CollectedFieldGroup.responseName).Nodup := by
  rw [← mappedGroupKeys executionParentType groups]
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
    (executionParentType responseName : Name)
    (executionFields : List ExecutableField)
    (executionTail : List (Name × List ExecutableField))
    (groups : List CollectedFieldGroup)
    (hequivalent
      : RuntimeGroupsPermutationEquivalent
          (groups.map
            (RuntimeCase.collectedFieldGroupToExecutableGroup executionParentType))
          ((responseName, executionFields) :: executionTail))
    : ∃ group staticTail,
        groups.Perm (group :: staticTail)
        ∧ group.responseName = responseName
        ∧ (RuntimeCase.collectedFieldGroupToExecutableGroup executionParentType
            group).2.Perm
            executionFields
        ∧ RuntimeGroupsPermutationEquivalent
            (staticTail.map
              (RuntimeCase.collectedFieldGroupToExecutableGroup executionParentType))
            executionTail := by
  have hright : responseName ∈ (((responseName, executionFields) :: executionTail).map
      Prod.fst) := by simp
  have hleft := (hequivalent.keys responseName).mpr hright
  rw [mappedGroupKeys executionParentType groups] at hleft
  rcases List.mem_map.mp hleft with ⟨group, hgroup, hname⟩
  rcases List.mem_iff_append.mp hgroup with ⟨before, after, hgroups⟩
  subst groups
  let staticTail := before ++ after
  have hperm :
      (before ++ group :: after).Perm (group :: staticTail) := by
    simp [staticTail]
  have hmappedPerm := hperm.map
    (RuntimeCase.collectedFieldGroupToExecutableGroup executionParentType)
  have haligned :=
    runtimeGroupsPermutationEquivalent_permuteLeft hequivalent hmappedPerm
  have hgroupName : group.responseName = responseName := hname
  have haligned' : RuntimeGroupsPermutationEquivalent
      ((responseName,
          (RuntimeCase.collectedFieldGroupToExecutableGroup executionParentType group).2)
        :: staticTail.map
          (RuntimeCase.collectedFieldGroupToExecutableGroup executionParentType))
      ((responseName, executionFields) :: executionTail) := by
    simpa [RuntimeCase.collectedFieldGroupToExecutableGroup, hgroupName] using haligned
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
          CaseForest.summarize algebra schema childParentType
            group.childInheritedBooleanCondition (.ofConditionTree childTree)
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
                  (CaseForest.summarize algebra schema first
                    group.childInheritedBooleanCondition
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
    (algebra : Algebra.{v}) (lawful : algebra.Lawful)
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
          ← RuntimeCase.summarize_eq_resolved algebra schema childParentType
            group.childInheritedBooleanCondition (.ofConditionTree childTree)
            childTree.condition.possibleTypes childRuntimeType variableValues
            fixedVariableValues]
        apply lawful.le_trans _
          (CaseForest.summarize algebra schema childParentType
            group.childInheritedBooleanCondition (.ofConditionTree childTree)
            childTree.condition.possibleTypes variableValues fixedVariableValues)
        · apply RuntimeCase.summarize_le algebra lawful schema childParentType
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

theorem mappedExecutableField_source
    (executionParentType : Name) (group : CollectedFieldGroup)
    (field : ExecutableField)
    (hfield
      : field
        ∈ (RuntimeCase.collectedFieldGroupToExecutableGroup executionParentType group).2)
    : field.parentType = executionParentType ∧ field.fieldName ∈ group.fieldNames := by
  unfold RuntimeCase.collectedFieldGroupToExecutableGroup at hfield
  rcases List.mem_filterMap.mp hfield with ⟨selection, hselection, hmapped⟩
  cases selection with
  | inlineFragment typeCondition directives selectionSet => simp at hmapped
  | field responseName fieldName arguments directives selectionSet =>
      simp only at hmapped
      cases hmapped
      refine ⟨rfl, ?_⟩
      simp [CollectedFieldGroup.selections, ConditionTree.FieldGroup.selections,
        ConditionTree.Field.toSelection] at hselection
      rcases hselection with
        ⟨candidate, hcandidate, _hresponseName, hfieldName, _⟩
      exact List.mem_map.mpr ⟨candidate, hcandidate, hfieldName⟩

theorem mappedExecutableField_represented
    (executionParentType : Name) (group : CollectedFieldGroup)
    (field : ExecutableField)
    (hfield
      : field
        ∈ (RuntimeCase.collectedFieldGroupToExecutableGroup executionParentType group).2)
    (hshape
      : ∀ selection,
          selection ∈ group.selections
          -> ∃ candidate : Field, selection = candidate.toSelection group.responseName)
    : groupRepresentsField group field := by
  unfold RuntimeCase.collectedFieldGroupToExecutableGroup at hfield
  rcases List.mem_filterMap.mp hfield with ⟨selection, hselection, hmapped⟩
  cases selection with
  | inlineFragment typeCondition directives selectionSet => simp at hmapped
  | field responseName fieldName arguments directives selectionSet =>
      simp only at hmapped
      cases hmapped
      rcases hshape (.field responseName fieldName arguments directives selectionSet)
          hselection with ⟨candidate, hcandidate⟩
      cases candidate
      simp [groupRepresentsField, Field.toSelection] at hcandidate ⊢
      simpa [hcandidate] using hselection

private theorem mergeSelectionSets_eq_flatMap (selections : List Selection)
    : SelectionSet.mergeSelectionSets selections
      = selections.flatMap Selection.subselections :=
  rfl

private theorem mappedExecutableFields_selectionSets
    (executionParentType responseName : Name) (selections : List Selection)
    (hshape
      : ∀ selection,
          selection ∈ selections
          -> ∃ field : Field, selection = field.toSelection responseName)
    : (selections.filterMap
        fun selection =>
          match selection with
          | .field selectedResponseName fieldName arguments _directives selectionSet =>
              some
                ({
                    parentType := executionParentType
                    responseName := selectedResponseName
                    fieldName
                    arguments
                    selectionSet
                  }
                  : ExecutableField)
          | .inlineFragment _typeCondition _directives _selectionSet => none).flatMap
        ExecutableField.selectionSet
      = selections.flatMap Selection.subselections := by
  induction selections with
  | nil => rfl
  | cons selection rest ih =>
      rcases hshape selection (by simp) with ⟨field, rfl⟩
      simp only [List.filterMap_cons, List.flatMap_cons, Field.toSelection,
        Selection.subselections]
      rw [ih (by
        intro candidate hcandidate
        exact hshape candidate (by simp [hcandidate]))]

theorem collectedFieldGroup_mergedSelectionSet_perm
    (executionParentType : Name) (group : CollectedFieldGroup)
    (fields : List ExecutableField)
    (hshape
      : ∀ selection,
          selection ∈ group.selections
          -> ∃ field : Field, selection = field.toSelection group.responseName)
    (hfields
      : (RuntimeCase.collectedFieldGroupToExecutableGroup executionParentType
          group).2.Perm
          fields)
    : group.mergedSelectionSet.Perm (Execution.mergedFieldSelectionSet fields) := by
  rw [CollectedFieldGroup.mergedSelectionSet,
    ConditionTree.FieldGroup.mergedSelectionSet, mergeSelectionSets_eq_flatMap]
  change (group.selections.flatMap Selection.subselections).Perm
    (Execution.mergedFieldSelectionSet fields)
  rw [← mappedExecutableFields_selectionSets executionParentType group.responseName
      group.selections hshape,
    ← mergedFieldSelectionSet_eq_flatMap]
  exact mergedFieldSelectionSet_perm hfields

theorem lookupField_outputType_mem_fieldOutputTypes
    (schema : Schema) (variableValues : VariableValues)
    (runtimeType : Name) (group : CollectedFieldGroup)
    (fieldName : Name) (definition : FieldDefinition)
    (hallows : group.condition.allows variableValues runtimeType = true)
    (hfieldName : fieldName ∈ group.fieldNames)
    (hlookup : schema.lookupField runtimeType fieldName = some definition)
    : definition.outputType ∈ group.fieldOutputTypes schema := by
  have hruntime : runtimeType ∈ group.condition.possibleTypes :=
    List.contains_iff_mem.mp (Bool.and_eq_true_iff.mp hallows).1
  unfold CollectedFieldGroup.fieldOutputTypes
  apply List.mem_flatMap.mpr
  refine ⟨runtimeType, hruntime, ?_⟩
  exact List.mem_filterMap.mpr ⟨fieldName, hfieldName, by simp [hlookup]⟩

theorem lookupField_childParentType_mem
    (schema : Schema) (variableValues : VariableValues)
    (runtimeType : Name) (group : CollectedFieldGroup)
    (fieldName : Name) (definition : FieldDefinition)
    (hallows : group.condition.allows variableValues runtimeType = true)
    (hfieldName : fieldName ∈ group.fieldNames)
    (hlookup : schema.lookupField runtimeType fieldName = some definition)
    : definition.outputType.namedType ∈ childParentTypes schema group := by
  unfold childParentTypes
  simp only [List.mem_eraseDups, List.mem_map]
  exact ⟨definition.outputType,
    lookupField_outputType_mem_fieldOutputTypes schema variableValues runtimeType group
      fieldName definition hallows hfieldName hlookup,
    rfl⟩

theorem Compatible.singleFieldResult_related
    {concrete : ConcreteAlgebra.{u}} {abstract : Algebra.{v}} {schema : Schema}
    (variableValues fixedVariableValues : VariableValues)
    (responseName : Name)
    (compatible : Compatible concrete abstract schema variableValues)
    (field : ExecutableField) (schemaDefinition : FieldDefinition)
    (completed : Result AnnotatedResponseValue)
    (group : CollectedFieldGroup)
    (hparent : field.parentType ∈ group.condition.possibleTypes)
    (hrepresents : groupRepresentsField group field)
    (hlookup
      : schema.lookupField field.parentType field.fieldName = some schemaDefinition)
    (houtput : schemaDefinition.outputType ∈ group.fieldOutputTypes schema)
    (hcompleted
      : compatible.related
          (foldAnnotatedResponseValueResult concrete completed)
          (foldChildSummaryForValueResult abstract
            (summarizedChildren abstract schema variableValues group fixedVariableValues)
            completed))
    : compatible.related
        (foldAnnotatedResponseFieldsResult concrete
          (singleAnnotatedResponseFieldResult schema variableValues schemaDefinition
            responseName field completed))
        (summarizedGroup abstract schema variableValues group fixedVariableValues) := by
  cases completed with
  | error errors => exact compatible.toCompatibilityCore.empty_related_any _
  | ok completed =>
      rcases completed with ⟨value, errors⟩
      have hfield := compatible.field_related group field schemaDefinition
        value (foldAnnotatedResponseValueChildren concrete value)
        (summarizedChildren abstract schema variableValues group fixedVariableValues)
        hparent hrepresents
        hlookup houtput hcompleted
      simpa [singleAnnotatedResponseFieldResult,
        resolvedFieldProvenance,
        foldAnnotatedResponseFieldsResult, foldAnnotatedResponseFields,
        summarizedGroup, summarizedChildren,
        compatible.concreteLawful.combine_empty] using hfield

-- The executor follows one exact terminal runtime case. Each recursive object value
-- extracts its own child case; list completion only repeats the same child summary.
private theorem annotatedResponseExecution_related_all
    {concrete : ConcreteAlgebra.{u}} {abstract : Algebra.{v}}
    (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variableValues fixedVariableValues : VariableValues)
    (hpruning : BooleanValuesMatchForPruning variableValues fixedVariableValues)
    (compatible : Compatible concrete abstract schema variableValues)
    : (∀ fuel source executionGroups,
        ∀ runtimeType (ref : ObjectRef) staticGroups,
          source = .object runtimeType ref
          -> RuntimeGroupsPermutationEquivalent
              (staticGroups.map
                (RuntimeCase.collectedFieldGroupToExecutableGroup runtimeType))
              executionGroups
          -> StaticGroupsValid variableValues runtimeType staticGroups
          -> compatible.related
              (foldAnnotatedResponseFieldsResult concrete
                (executeQueryAnnotatedCollectedFields schema resolvers variableValues fuel
                  source executionGroups))
              (summarizeCollectedGroups abstract schema variableValues staticGroups
                fixedVariableValues))
      ∧ (∀ fuel source responseName fields,
          ∀ runtimeType (ref : ObjectRef) group,
            source = .object runtimeType ref
            -> group.responseName = responseName
            -> (RuntimeCase.collectedFieldGroupToExecutableGroup runtimeType group).2.Perm
                fields
            -> StaticGroupsValid variableValues runtimeType [group]
            -> compatible.related
                (foldAnnotatedResponseFieldsResult concrete
                  (executeQueryAnnotatedField schema resolvers variableValues fuel source
                    responseName fields))
                (summarizedGroup abstract schema variableValues group
                  fixedVariableValues))
      ∧ (∀ fuel fieldType fields value,
          ∀ runtimeType (_ref : ObjectRef) fieldName definition group,
            fieldType.namedType = definition.outputType.namedType
            -> schema.lookupField runtimeType fieldName = some definition
            -> definition.outputType ∈ group.fieldOutputTypes schema
            -> (RuntimeCase.collectedFieldGroupToExecutableGroup runtimeType group).2.Perm
                fields
            -> StaticGroupsValid variableValues runtimeType [group]
            -> compatible.related
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
            -> (RuntimeCase.collectedFieldGroupToExecutableGroup runtimeType group).2.Perm
                fields
            -> StaticGroupsValid variableValues runtimeType [group]
            -> compatible.related
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
    intro fuel source runtimeType ref staticGroups _hsource _hequivalent _hvalid
    simpa [executeQueryAnnotatedCollectedFields,
      foldAnnotatedResponseFieldsResult, foldAnnotatedResponseFields] using
      compatible.toCompatibilityCore.empty_related_any
        (summarizeCollectedGroups abstract schema variableValues staticGroups
          fixedVariableValues)
  case case2 =>
    intro fuel source responseName fields rest field_ih tail_ih runtimeType ref
      staticGroups hsource hequivalent hvalid
    subst source
    rcases alignStaticGroup runtimeType responseName fields rest staticGroups hequivalent
      with ⟨group, staticTail, hperm, hname, hfields, htailEquivalent⟩
    have hvalid' := hvalid.perm hperm
    have hhead := field_ih runtimeType ref group rfl hname hfields (by
      intro candidate hcandidate
      have heq : candidate = group := List.mem_singleton.mp hcandidate
      subst candidate
      exact hvalid' group (by simp))
    have htail := tail_ih runtimeType ref staticTail rfl htailEquivalent (by
      intro candidate hcandidate
      exact hvalid' candidate (by simp [hcandidate]))
    have hcombine := compatible.toCompatibilityCore.combineFieldsResult_related _ _ _ _ hhead htail
    rw [executeQueryAnnotatedCollectedFields]
    rw [summarizeCollectedGroups_perm abstract compatible.abstractLawful schema
      variableValues fixedVariableValues hperm]
    exact hcombine
  case case3 =>
    intro fuel source responseName runtimeType ref group _hsource _hname hfields hvalid
    have hnonempty := (hvalid group (by simp)).2.2.1
    have hmappedNonempty :
        (RuntimeCase.collectedFieldGroupToExecutableGroup runtimeType group).2 ≠ [] := by
      intro hempty
      unfold RuntimeCase.collectedFieldGroupToExecutableGroup at hempty
      have hshape := (hvalid group (by simp)).2.2.2
      cases hgroups : group.selections with
      | nil => exact hnonempty hgroups
      | cons selection rest =>
          rcases hshape selection (by simp [hgroups]) with ⟨field, hfield⟩
          subst selection
          simp [hgroups, Field.toSelection] at hempty
    exact False.elim (hmappedNonempty (List.Perm.eq_nil hfields))
  case case4 =>
    intro source responseName field rest runtimeType ref group _hsource _hname _hfields
      _hvalid
    simpa [executeQueryAnnotatedField, foldAnnotatedResponseFieldsResult] using
      compatible.toCompatibilityCore.empty_related_any
        (summarizedGroup abstract schema variableValues group fixedVariableValues)
  case case5 =>
    intro source responseName field rest fuel hlookup runtimeType ref group _hsource
      _hname _hfields _hvalid
    simpa [executeQueryAnnotatedField, hlookup,
      foldAnnotatedResponseFieldsResult] using
      compatible.toCompatibilityCore.empty_related_any
        (summarizedGroup abstract schema variableValues group fixedVariableValues)
  case case6 =>
    intro source responseName field rest fuel definition hlookup hcoerce runtimeType ref
      group hsource hname hfields hvalid
    subst source
    have hfieldMem : field ∈
        (RuntimeCase.collectedFieldGroupToExecutableGroup runtimeType group).2 :=
      (hfields.mem_iff).mpr (by simp)
    rcases mappedExecutableField_source runtimeType group field hfieldMem with
      ⟨hparent, hfieldName⟩
    have hlookupRuntime : schema.lookupField runtimeType field.fieldName = some definition :=
      by simpa [hparent] using hlookup
    have hcondition := (hvalid group (by simp)).2.1
    have hparentPossible : field.parentType ∈ group.condition.possibleTypes := by
      rw [hparent]
      exact List.contains_iff_mem.mp (Bool.and_eq_true_iff.mp hcondition).1
    have hrepresents := mappedExecutableField_represented runtimeType group field
      hfieldMem (hvalid group (by simp)).2.2.2
    have houtput := lookupField_outputType_mem_fieldOutputTypes schema variableValues
      runtimeType group field.fieldName definition hcondition hfieldName hlookupRuntime
    let completed : Result AnnotatedResponseValue :=
      match definition.outputType with
      | .nonNull _inner => .error 1
      | _ => .ok (.null, 1)
    have hcompleted : compatible.related
        (foldAnnotatedResponseValueResult concrete completed)
        (foldChildSummaryForValueResult abstract
          (summarizedChildren abstract schema variableValues group
            fixedVariableValues) completed) := by
      cases htype : definition.outputType <;>
        simp [completed, htype, foldAnnotatedResponseValueResult,
          foldAnnotatedResponseValueChildren, foldChildSummaryForValueResult,
          foldChildSummaryForValue] <;>
        exact compatible.toCompatibilityCore.empty_related_any _
    have hsingle := compatible.singleFieldResult_related variableValues
      fixedVariableValues responseName field definition completed group hparentPossible
      hrepresents hlookup houtput hcompleted
    simp only [executeQueryAnnotatedField, hlookup]
    rw [hcoerce]
    exact hsingle
  case case7 =>
    intro source responseName field rest fuel definition hlookup coercedArguments hcoerce
      hresolve runtimeType ref group hsource hname hfields hvalid
    subst source
    have hfieldMem : field ∈
        (RuntimeCase.collectedFieldGroupToExecutableGroup runtimeType group).2 :=
      (hfields.mem_iff).mpr (by simp)
    rcases mappedExecutableField_source runtimeType group field hfieldMem with
      ⟨hparent, hfieldName⟩
    have hlookupRuntime : schema.lookupField runtimeType field.fieldName = some definition :=
      by simpa [hparent] using hlookup
    have hcondition := (hvalid group (by simp)).2.1
    have hparentPossible : field.parentType ∈ group.condition.possibleTypes := by
      rw [hparent]
      exact List.contains_iff_mem.mp (Bool.and_eq_true_iff.mp hcondition).1
    have hrepresents := mappedExecutableField_represented runtimeType group field
      hfieldMem (hvalid group (by simp)).2.2.2
    have houtput := lookupField_outputType_mem_fieldOutputTypes schema variableValues
      runtimeType group field.fieldName definition hcondition hfieldName hlookupRuntime
    let completed : Result AnnotatedResponseValue :=
      match definition.outputType with
      | .nonNull _inner => .error 1
      | _ => .ok (.null, 1)
    have hcompleted : compatible.related
        (foldAnnotatedResponseValueResult concrete completed)
        (foldChildSummaryForValueResult abstract
          (summarizedChildren abstract schema variableValues group
            fixedVariableValues) completed) := by
      cases htype : definition.outputType <;>
        simp [completed, htype, foldAnnotatedResponseValueResult,
          foldAnnotatedResponseValueChildren, foldChildSummaryForValueResult,
          foldChildSummaryForValue] <;>
        exact compatible.toCompatibilityCore.empty_related_any _
    have hsingle := compatible.singleFieldResult_related variableValues
      fixedVariableValues responseName field definition completed group hparentPossible
      hrepresents hlookup houtput hcompleted
    simp only [executeQueryAnnotatedField, hlookup, hcoerce]
    rw [hresolve]
    exact hsingle
  case case8 =>
    intro source responseName field rest fuel definition hlookup coercedArguments hcoerce
      resolved hresolve
      complete_ih runtimeType ref group hsource hname hfields hvalid
    subst source
    have hfieldMem : field ∈
        (RuntimeCase.collectedFieldGroupToExecutableGroup runtimeType group).2 :=
      (hfields.mem_iff).mpr (by simp)
    rcases mappedExecutableField_source runtimeType group field hfieldMem with
      ⟨hparent, hfieldName⟩
    have hlookupRuntime : schema.lookupField runtimeType field.fieldName = some definition :=
      by simpa [hparent] using hlookup
    have hcondition := (hvalid group (by simp)).2.1
    have hparentPossible : field.parentType ∈ group.condition.possibleTypes := by
      rw [hparent]
      exact List.contains_iff_mem.mp (Bool.and_eq_true_iff.mp hcondition).1
    have hrepresents := mappedExecutableField_represented runtimeType group field
      hfieldMem (hvalid group (by simp)).2.2.2
    have houtput := lookupField_outputType_mem_fieldOutputTypes schema variableValues
      runtimeType group field.fieldName definition hcondition hfieldName hlookupRuntime
    have hcompleted := complete_ih runtimeType ref field.fieldName definition
      group rfl hlookupRuntime houtput hfields hvalid
    have hsingle := compatible.singleFieldResult_related variableValues
      fixedVariableValues responseName field definition
      (completeAnnotatedResponseValue schema resolvers variableValues fuel
        definition.outputType (field :: rest) resolved)
      group hparentPossible hrepresents hlookup houtput hcompleted
    simpa [executeQueryAnnotatedField, hlookup, hcoerce, hresolve] using hsingle
  case case9 =>
    intro fieldType fields value runtimeType ref fieldName definition group
      _hnamed _hlookup _houtput _hfields _hvalid
    simpa [completeAnnotatedResponseValue, foldAnnotatedResponseValueResult,
      foldChildSummaryForValueResult] using
      compatible.empty_related
  case case10 =>
    intro fuel inner fields value hfuel complete_ih runtimeType ref fieldName
      definition group hnamed hlookup houtput hfields hvalid
    have hinner := complete_ih runtimeType ref fieldName definition group
      (by simpa [TypeRef.namedType] using hnamed) hlookup houtput hfields hvalid
    simpa [completeAnnotatedResponseValue, hfuel] using
      compatible.toCompatibilityCore.completeNonNullResult_related
        (completeAnnotatedResponseValue schema resolvers variableValues fuel inner fields
          value)
        (summarizedChildren abstract schema variableValues group fixedVariableValues)
        hinner
  case case11 =>
    intro fuel fieldType fields hnotNonNull runtimeType ref fieldName
      definition group _hnamed _hlookup _houtput _hfields _hvalid
    simpa [completeAnnotatedResponseValue, hnotNonNull,
      foldAnnotatedResponseValueResult, foldAnnotatedResponseValueChildren,
      foldChildSummaryForValueResult, foldChildSummaryForValue] using
      compatible.empty_related
  case case12 =>
    intro fuel typeName fields value hcomposite runtimeType ref fieldName
      definition group _hnamed _hlookup _houtput _hfields _hvalid
    simpa [completeAnnotatedResponseValue, hcomposite,
      foldAnnotatedResponseValueResult, foldChildSummaryForValueResult] using
      compatible.empty_related
  case case13 =>
    intro fuel typeName fields value hnotComposite runtimeType ref fieldName
      definition group _hnamed _hlookup _houtput _hfields _hvalid
    have hcomposite : (TypeRef.named typeName).isCompositeBool schema = false := by
      cases hvalue : (TypeRef.named typeName).isCompositeBool schema with
      | false => rfl
      | true => exact False.elim (hnotComposite hvalue)
    simpa [completeAnnotatedResponseValue, hcomposite,
      foldAnnotatedResponseValueResult, foldAnnotatedResponseValueChildren,
      foldChildSummaryForValueResult, foldChildSummaryForValue] using
      compatible.empty_related
  case case14 =>
    intro fuel childParentType fields childRuntimeType childRef hinclude childGroups
      child_ih runtimeType ref fieldName definition group hnamed hlookup
      houtput hfields hvalid
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
      collectedFieldGroup_mergedSelectionSet_perm runtimeType group fields
        (hvalid group (by simp)).2.2.2 hfields
    have hchildInherited : booleanConditionAllows variableValues
        group.childInheritedBooleanCondition = true :=
      ConditionTree.childInheritedBooleanCondition_allows variableValues
        group.inheritedBooleanCondition group.condition.booleanCondition
        (hvalid group (by simp)).1
        (Bool.and_eq_true_iff.mp (hvalid group (by simp)).2.1).2
    have hchildEquivalent : RuntimeGroupsPermutationEquivalent
        (childStaticGroups.map
          (RuntimeCase.collectedFieldGroupToExecutableGroup childRuntimeType))
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
    have hchild := child_ih childRuntimeType childRef childStaticGroups rfl
      hchildEquivalent hchildValid
    have hcandidatesLe : compatible.abstractLawful.le
        (summarizeCollectedGroups abstract schema variableValues childStaticGroups
          fixedVariableValues)
        (summarizedChildren abstract schema variableValues group
          fixedVariableValues) := by
      have hchildType : definition.outputType.namedType ∈ childParentTypes schema group := by
        unfold childParentTypes
        simp only [List.mem_eraseDups, List.mem_map]
        exact ⟨definition.outputType, houtput, rfl⟩
      have hbound := candidateChildGroupsFor_le_summarizeCollectedChildren abstract
        compatible.abstractLawful schema variableValues fixedVariableValues
        definition.outputType.namedType childRuntimeType [group]
        (List.contains_iff_mem.mp hpossible)
        (by
          intro candidate hcandidate
          have heq : candidate = group := List.mem_singleton.mp hcandidate
          simpa [heq] using hchildType)
      simpa [candidateChildGroupsFor, childStaticGroups, summarizeCollectedChildren,
        summarizedChildren, compatible.abstractLawful.combine_empty] using hbound
    have hchild' := compatible.related_mono _ _ _ hchild hcandidatesLe
    cases hresult : executeQueryAnnotatedCollectedFields schema resolvers variableValues fuel
        (.object childRuntimeType childRef) childGroups with
    | error errors =>
        have hresult' :
            executeQueryAnnotatedCollectedFields schema resolvers variableValues fuel
                (.object childRuntimeType childRef)
                (collectFields schema variableValues childRuntimeType
                  (.object childRuntimeType childRef)
                  (Execution.mergedFieldSelectionSet fields))
              = .error errors := by
          simpa [childGroups,
            NormalForm.collectSubfields_eq_collectFields_mergedFieldSelectionSet] using
            hresult
        simpa [completeAnnotatedResponseValue, hinclude, hresult',
          catchAnnotatedResponseBubbleAsNull,
          foldAnnotatedResponseValueResult, foldAnnotatedResponseValueChildren,
          foldChildSummaryForValueResult, foldChildSummaryForValue] using
          compatible.empty_related
    | ok completed =>
        rcases completed with ⟨childFields, errors⟩
        rw [hresult] at hchild'
        have hresult' :
            executeQueryAnnotatedCollectedFields schema resolvers variableValues fuel
                (.object childRuntimeType childRef)
                (collectFields schema variableValues childRuntimeType
                  (.object childRuntimeType childRef)
                  (Execution.mergedFieldSelectionSet fields))
              = .ok (childFields, errors) := by
          simpa [childGroups,
            NormalForm.collectSubfields_eq_collectFields_mergedFieldSelectionSet] using
            hresult
        have hchildFields : compatible.related
            (foldAnnotatedResponseFields concrete childFields)
            (summarizedChildren abstract schema variableValues group
              fixedVariableValues) := by
          simpa [foldAnnotatedResponseFieldsResult] using hchild'
        simpa [completeAnnotatedResponseValue, hinclude, hresult',
          catchAnnotatedResponseBubbleAsNull,
          foldAnnotatedResponseValueResult, foldAnnotatedResponseValueChildren,
          foldChildSummaryForValueResult, foldChildSummaryForValue,
          compatible.abstractLawful.combine_empty] using hchildFields
  case case15 =>
    intro fuel parentType fields childRuntimeType childRef hnotInclude runtimeType ref
      fieldName definition group _hnamed _hlookup _houtput _hfields _hvalid
    have hinclude : schema.typeIncludesObjectBool parentType childRuntimeType = false := by
      cases hvalue : schema.typeIncludesObjectBool parentType childRuntimeType with
      | false => rfl
      | true => exact False.elim (hnotInclude hvalue)
    simpa [completeAnnotatedResponseValue, hinclude,
      foldAnnotatedResponseValueResult, foldChildSummaryForValueResult] using
      compatible.empty_related
  case case16 =>
    intro fuel inner fields values list_ih runtimeType ref fieldName
      definition group hnamed hlookup houtput hfields hvalid
    have hlist := list_ih runtimeType ref fieldName definition group
      (by simpa [TypeRef.namedType] using hnamed) hlookup houtput hfields hvalid
    cases hresult : completeAnnotatedResponseValueList schema resolvers variableValues fuel
        inner fields values with
    | error errors =>
        simpa [completeAnnotatedResponseValue, hresult,
          catchAnnotatedResponseBubbleAsNull,
          foldAnnotatedResponseValueResult, foldAnnotatedResponseValueChildren,
          foldChildSummaryForValueResult, foldChildSummaryForValue] using
          compatible.empty_related
    | ok completed =>
        rcases completed with ⟨completedValues, errors⟩
        rw [hresult] at hlist
        have hvalues : compatible.related
            (foldAnnotatedResponseValues concrete completedValues)
            (foldChildSummaryForValues abstract
              (summarizedChildren abstract schema variableValues group
                fixedVariableValues)
              completedValues) := by
          simpa [foldAnnotatedResponseValuesResult,
            foldChildSummaryForValuesResult] using hlist
        simpa [completeAnnotatedResponseValue, hresult,
          catchAnnotatedResponseBubbleAsNull,
          foldAnnotatedResponseValueResult, foldAnnotatedResponseValueChildren,
          foldChildSummaryForValueResult, foldChildSummaryForValue] using hvalues
  case case17 =>
    intro fuel typeName fields values runtimeType ref fieldName definition
      group _hnamed _hlookup _houtput _hfields _hvalid
    simpa [completeAnnotatedResponseValue, foldAnnotatedResponseValueResult,
      foldChildSummaryForValueResult] using
      compatible.empty_related
  case case18 =>
    intro fuel inner fields value hnotNull hnotList runtimeType ref fieldName
      definition group _hnamed _hlookup _houtput _hfields _hvalid
    simpa [completeAnnotatedResponseValue, hnotNull, hnotList,
      foldAnnotatedResponseValueResult, foldChildSummaryForValueResult] using
      compatible.empty_related
  case case19 =>
    intro fuel itemType fields runtimeType ref fieldName definition group
      _hnamed _hlookup _houtput _hfields _hvalid
    simpa [completeAnnotatedResponseValueList,
      foldAnnotatedResponseValuesResult, foldAnnotatedResponseValues,
      foldChildSummaryForValuesResult, foldChildSummaryForValues] using
      compatible.empty_related
  case case20 =>
    intro fuel itemType fields value values head_ih tail_ih runtimeType ref
      fieldName definition group hnamed hlookup houtput hfields hvalid
    have hhead := head_ih runtimeType ref fieldName definition group hnamed
      hlookup houtput hfields hvalid
    have htail := tail_ih runtimeType ref fieldName definition group hnamed
      hlookup houtput hfields hvalid
    simpa [completeAnnotatedResponseValueList] using
      compatible.toCompatibilityCore.combineValuesResult_related
        (completeAnnotatedResponseValue schema resolvers variableValues fuel itemType fields
          value)
        (completeAnnotatedResponseValueList schema resolvers variableValues fuel itemType
          fields values)
        (summarizedChildren abstract schema variableValues group fixedVariableValues)
        hhead htail

private theorem Compatible.executeQueryAnnotatedWithFuel_relatedAt
    {concrete : ConcreteAlgebra.{u}} {abstract : Algebra.{v}} {schema : Schema}
    (operation : Operation) (resolvers : Resolvers ObjectRef)
    (variableValues : VariableValues)
    (pruningValues : VariableValues)
    (hmatch
      : BooleanValuesMatchForPruning
          (coerceVariableValues operation variableValues) pruningValues)
    (compatible
      : Compatible concrete abstract schema
          (coerceVariableValues operation variableValues))
    (fuel : Nat)
    (source : ResolverValue ObjectRef)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (hoperation : Validation.operationDefinitionValid schema operation)
    : compatible.related
        (foldAnnotatedResponse concrete
          (executeQueryAnnotatedWithFuel schema resolvers variableValues operation fuel
            source))
        (summarizeSelectionSetResolved abstract schema (operation.rootType schema) []
          operation.selectionSet (coerceVariableValues operation variableValues)
          pruningValues) := by
  have hrootObject : schema.objectType (operation.rootType schema) := by
    rw [Validation.operationDefinitionValid_rootType_eq hoperation]
    exact hschema.2.1
  let coercedVariableValues := coerceVariableValues operation variableValues
  cases hroot : rootSourceAppliesBool schema operation source with
  | false =>
      simpa [executeQueryAnnotatedWithFuel, hroot, foldAnnotatedResponse,
        foldAnnotatedResponseValueChildren] using
        compatible.toCompatibilityCore.empty_related_any
          (summarizeSelectionSetResolved abstract schema (operation.rootType schema) []
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
      let staticGroups := RuntimeCase.fieldGroups (operation.rootType schema) []
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
          (staticGroups.map
            (RuntimeCase.collectedFieldGroupToExecutableGroup (operation.rootType schema)))
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
      have hrelated :=
        (annotatedResponseExecution_related_all schema resolvers coercedVariableValues
          pruningValues hmatch compatible).1 fuel
          (.object (operation.rootType schema) ref) executionGroups
          (operation.rootType schema) ref staticGroups rfl hequivalent hvalid
      have hsummaryLe : compatible.abstractLawful.le
          (summarizeCollectedGroups abstract schema coercedVariableValues staticGroups
            pruningValues)
          (summarizeSelectionSetResolved abstract schema (operation.rootType schema) []
            operation.selectionSet coercedVariableValues pruningValues) := by
        rw [summarizeCollectedGroups_eq abstract schema coercedVariableValues
          pruningValues _]
        rw [← RuntimeCase.summarize_eq_resolved abstract schema
          (operation.rootType schema) [] (.ofConditionTree tree)
          tree.condition.possibleTypes (operation.rootType schema)
          coercedVariableValues pruningValues]
        simpa [summarizeSelectionSetResolved, summarizeConditionTreeResolved,
          tree] using
          RuntimeCase.summarize_le abstract compatible.abstractLawful schema
            (operation.rootType schema) [] (.ofConditionTree tree)
            tree.condition.possibleTypes (operation.rootType schema)
            coercedVariableValues pruningValues htreePossible
      have hrelated' := compatible.related_mono _ _ _ hrelated hsummaryLe
      cases hresult
            : executeQueryAnnotatedCollectedFields schema resolvers
                coercedVariableValues fuel (.object (operation.rootType schema) ref)
                executionGroups with
      | error errors =>
          rw [hresult] at hrelated'
          simpa [executeQueryAnnotatedWithFuel, hroot, coercedVariableValues,
            executionGroups, hresult, foldAnnotatedResponse,
            foldAnnotatedResponseValueChildren,
            foldAnnotatedResponseFieldsResult] using hrelated'
      | ok completed =>
          rcases completed with ⟨fields, errors⟩
          rw [hresult] at hrelated'
          simpa [executeQueryAnnotatedWithFuel, hroot, coercedVariableValues,
            executionGroups, hresult, foldAnnotatedResponse,
            foldAnnotatedResponseValueChildren,
            foldAnnotatedResponseFieldsResult] using hrelated'

private theorem Compatible.executeQueryAnnotatedWithFuel_relatedResolvedContext
    {concrete : ConcreteAlgebra.{u}} {abstract : Algebra.{v}} {schema : Schema}
    (operation : Operation) (resolvers : Resolvers ObjectRef)
    (variableValues : VariableValues)
    (compatible
      : Compatible concrete abstract schema
          (coerceVariableValues operation variableValues))
    (fuel : Nat) (source : ResolverValue ObjectRef)
    (environment : BooleanEnvironment)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (hoperation : Validation.operationDefinitionValid schema operation)
    (hvalues : environment.variableValues = coerceVariableValues operation variableValues)
    (hfixed
      : environment.fixedVariableValues = coerceVariableValues operation variableValues)
    (hresolved : environment.ResolvedFor (operationBooleanVariables operation))
    : compatible.related
        (foldAnnotatedResponse concrete
          (executeQueryAnnotatedWithFuel schema resolvers variableValues operation fuel
            source))
        (summarizeSelectionSet abstract schema (operation.rootType schema) []
          operation.selectionSet environment) := by
  let coercedVariableValues := coerceVariableValues operation variableValues
  have htreeResolved :
      environment.ResolvedFor
        (conditionTreeBooleanVariables
          (ConditionTree.ofSelectionSetInScopeWithKnownFalsePruning schema
            (operation.rootType schema) [] environment.fixedVariableValues
            operation.selectionSet)).eraseDups := by
    intro variableName hvariable
    apply hresolved variableName
    simp only [operationBooleanVariables, List.mem_eraseDups]
    apply ConditionTree.ofSelectionSetInScopeWithKnownFalsePruning_booleanVariablesWithin schema
      (operation.rootType schema) [] environment.fixedVariableValues
      operation.selectionSet variableName
    simpa only [List.mem_eraseDups] using hvariable
  have hsummary :=
    summarizeSelectionSet_eq_resolved_of_resolvedFor abstract schema
      (operation.rootType schema) [] operation.selectionSet environment htreeResolved
  have hrelated :=
    Compatible.executeQueryAnnotatedWithFuel_relatedAt operation resolvers
      variableValues environment.fixedVariableValues
      (by rw [hfixed]; intro variableName value hvalue; simp [hvalue])
      compatible fuel source hschema hoperation
  rw [hfixed] at hrelated
  rw [hsummary, hvalues, hfixed]
  simpa [coercedVariableValues] using hrelated

private theorem Compatible.executeQueryAnnotated_relatedResolvedContext
    {concrete : ConcreteAlgebra.{u}} {abstract : Algebra.{v}} {schema : Schema}
    (operation : Operation) (resolvers : Resolvers ObjectRef)
    (variableValues : VariableValues)
    (compatible
      : Compatible concrete abstract schema
          (coerceVariableValues operation variableValues))
    (source : ResolverValue ObjectRef) (environment : BooleanEnvironment)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (hoperation : Validation.operationDefinitionValid schema operation)
    (hvalues : environment.variableValues = coerceVariableValues operation variableValues)
    (hfixed
      : environment.fixedVariableValues = coerceVariableValues operation variableValues)
    (hresolved : environment.ResolvedFor (operationBooleanVariables operation))
    : compatible.related
        (foldAnnotatedResponse concrete
          (executeQueryAnnotated schema resolvers variableValues operation source))
        (summarizeSelectionSet abstract schema (operation.rootType schema) []
          operation.selectionSet environment) := by
  simpa [executeQueryAnnotated] using
    Compatible.executeQueryAnnotatedWithFuel_relatedResolvedContext operation resolvers
      variableValues compatible (executeQueryFuelBound schema operation) source environment
      hschema hoperation hvalues hfixed hresolved

theorem operationContextWithVariablesSound
    {concrete : ConcreteAlgebra.{u}}
    (algebraFor : VariableValues -> Algebra.{v}) {schema : Schema}
    (compatibleFor : ∀ values, Compatible concrete (algebraFor values) schema values)
    (operation : Operation)
    : OperationContextWithVariablesSound algebraFor compatibleFor operation := by
  intro hschema hoperation ObjectRef resolvers variableValues source environment
  dsimp only
  intro hvalues hfixed hresolved
  let coercedVariableValues := coerceVariableValues operation variableValues
  exact Compatible.executeQueryAnnotated_relatedResolvedContext operation resolvers
    variableValues (compatibleFor coercedVariableValues) source environment hschema
    hoperation hvalues hfixed hresolved

theorem operationContextSound
    {concrete : ConcreteAlgebra.{u}} {abstract : Algebra.{v}} {schema : Schema}
    (compatibleFor : ∀ values, Compatible concrete abstract schema values)
    (operation : Operation)
    : OperationContextSound compatibleFor operation := by
  intro hschema hoperation ObjectRef resolvers variableValues source environment
  dsimp only
  intro hvalues hfixed hresolved
  let coercedVariableValues := coerceVariableValues operation variableValues
  exact Compatible.executeQueryAnnotated_relatedResolvedContext operation resolvers
    variableValues (compatibleFor coercedVariableValues) source environment hschema
    hoperation hvalues hfixed hresolved

theorem Compatible.executeQueryAnnotatedWithFuel_related
    {concrete : ConcreteAlgebra.{u}} {abstract : Algebra.{v}} {schema : Schema}
    (operation : Operation) (resolvers : Resolvers ObjectRef)
    (variableValues : VariableValues)
    (compatible
      : Compatible concrete abstract schema
          (coerceVariableValues operation variableValues))
    (fuel : Nat) (source : ResolverValue ObjectRef)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (hoperation : Validation.operationDefinitionValid schema operation)
    : compatible.related
        (foldAnnotatedResponse concrete
          (executeQueryAnnotatedWithFuel schema resolvers variableValues operation fuel
            source))
        (summarizeOperation abstract schema operation) := by
  let coercedVariableValues := coerceVariableValues operation variableValues
  have hresolved :=
    Compatible.executeQueryAnnotatedWithFuel_relatedAt operation resolvers
      variableValues []
      (by intro variableName value hvalue;
          simp [inputValueBoolean?, lookupVariableValue?] at hvalue)
      compatible fuel source hschema hoperation
  have hforget := summarizeOperationResolved_le_unknown abstract
    compatible.abstractLawful schema operation coercedVariableValues
  exact compatible.related_mono _ _ _ hresolved hforget

theorem Compatible.executeQueryAnnotated_related
    {concrete : ConcreteAlgebra.{u}} {abstract : Algebra.{v}} {schema : Schema}
    (operation : Operation) (resolvers : Resolvers ObjectRef)
    (variableValues : VariableValues)
    (compatible
      : Compatible concrete abstract schema
          (coerceVariableValues operation variableValues))
    (source : ResolverValue ObjectRef)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (hoperation : Validation.operationDefinitionValid schema operation)
    : compatible.related
        (foldAnnotatedResponse concrete
          (executeQueryAnnotated schema resolvers variableValues operation source))
        (summarizeOperation abstract schema operation) := by
  simpa [executeQueryAnnotated] using
    Compatible.executeQueryAnnotatedWithFuel_related operation resolvers
      variableValues compatible (executeQueryFuelBound schema operation) source
      hschema hoperation

theorem operationSoundWithFuel
    {concrete : ConcreteAlgebra.{u}} {abstract : Algebra.{v}} {schema : Schema}
    (compatibleFor : ∀ values, Compatible concrete abstract schema values)
    (operation : Operation)
    : OperationSoundWithFuel compatibleFor operation := by
  intro hschema hoperation ObjectRef resolvers variableValues fuel source
  let coercedVariableValues := coerceVariableValues operation variableValues
  exact Compatible.executeQueryAnnotatedWithFuel_related operation resolvers
    variableValues (compatibleFor coercedVariableValues) fuel source hschema hoperation

theorem operationSound
    {concrete : ConcreteAlgebra.{u}} {abstract : Algebra.{v}} {schema : Schema}
    (compatibleFor : ∀ values, Compatible concrete abstract schema values)
    (operation : Operation)
    : OperationSound compatibleFor operation := by
  intro hschema hoperation ObjectRef resolvers variableValues source
  let coercedVariableValues := coerceVariableValues operation variableValues
  exact Compatible.executeQueryAnnotated_related operation resolvers variableValues
    (compatibleFor coercedVariableValues) source hschema hoperation

theorem operationWithVariablesSoundWithFuel
    {concrete : ConcreteAlgebra.{u}}
    (algebraFor : VariableValues -> Algebra.{v}) {schema : Schema}
    (compatibleFor : ∀ values, Compatible concrete (algebraFor values) schema values)
    (operation : Operation)
    : OperationWithVariablesSoundWithFuel algebraFor compatibleFor operation := by
  intro hschema hoperation ObjectRef resolvers variableValues fuel source
  let coercedVariableValues := coerceVariableValues operation variableValues
  have hrelated :=
    Compatible.executeQueryAnnotatedWithFuel_relatedAt operation resolvers variableValues
      coercedVariableValues (by intro variableName value hvalue; rw [hvalue]; rfl)
      (compatibleFor coercedVariableValues) fuel source hschema hoperation
  simpa [summarizeOperationWithVariables, summarizeSelectionSetResolved,
    summarizeConditionTreeResolved, coercedVariableValues] using hrelated

theorem operationWithVariablesSound
    {concrete : ConcreteAlgebra.{u}}
    (algebraFor : VariableValues -> Algebra.{v}) {schema : Schema}
    (compatibleFor : ∀ values, Compatible concrete (algebraFor values) schema values)
    (operation : Operation)
    : OperationWithVariablesSound algebraFor compatibleFor operation := by
  intro hschema hoperation ObjectRef resolvers variableValues source
  have hsound := operationWithVariablesSoundWithFuel algebraFor compatibleFor operation
    hschema hoperation ObjectRef resolvers variableValues
    (executeQueryFuelBound schema operation) source
  simpa [executeQueryAnnotated] using hsound

theorem analysisWithVariablesSound
    (algebraFor : VariableValues -> Algebra.{v}) (schema : Schema)
    (operation : Operation)
    : AnalysisWithVariablesSound algebraFor schema operation := by
  intro concrete compatibleFor
  exact operationWithVariablesSound algebraFor compatibleFor operation

-- Generic witness for the public exact-case analysis soundness statement.
theorem analysisSound (abstract : Algebra.{v}) (schema : Schema) (operation : Operation)
    : AnalysisSound abstract schema operation := by
  intro concrete compatibleFor
  exact operationSound compatibleFor operation

end ExactCases
end TreeSummary
end GraphQL
