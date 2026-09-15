import GraphQL.Theories.ConditionTree.Reduce
import Proofs.GraphQL.Theories.ConditionTree.RuntimeExtraction
import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.FieldSemantics

/-! Runtime bundle construction and structural correspondence for reduction. -/

namespace GraphQL
namespace ConditionTree

open GraphQL.Execution
open NormalForm.GroundTypeNormalization
open NormalForm.GroundTypeNormalization.ReorderingSoundness
open RuntimeExtraction
open Execution.FieldGroups

-----------------------------------------------------------------------------------------
-- Runtime collection of reduced syntax
-----------------------------------------------------------------------------------------

def Field.toExecutable (field : Field) : ExecutableField :=
  {
    fieldName := field.fieldName
    arguments := field.arguments
    selectionSet := field.selectionSet
  }

def FieldGroup.reducedExecutableFields
    (schema : Schema) (parentType : Name)
    (inheritedBooleanCondition : List BooleanLiteral) (condition : Condition)
    (group : FieldGroup)
    : List (Name × ExecutableField) :=
  match schema.lookupField parentType group.first.fieldName with
  | none =>
      group.fields.map
        fun field =>
          (group.responseName, Field.toExecutable field)
  | some fieldDefinition =>
      let childInheritedBooleanCondition :=
        (canonicalBooleanCondition
          (inheritedBooleanCondition ++ condition.booleanCondition)).getD
          inheritedBooleanCondition
      [(
        group.responseName,
        {
          fieldName := group.first.fieldName
          arguments := group.first.arguments
          selectionSet :=
            reduceInScope schema fieldDefinition.outputType.namedType
              childInheritedBooleanCondition group.mergedSelectionSet
        }
      )]

mutual
  def Tree.reducedRuntimeFields
      (schema : Schema) (variableValues : VariableValues)
      (parentType runtimeType : Name)
      (inheritedBooleanCondition : List BooleanLiteral) (tree : Tree)
      : List (Name × ExecutableField) :=
    if tree.condition.allows variableValues runtimeType then
      tree.fields.flatMap
        (FieldGroup.reducedExecutableFields schema parentType
          inheritedBooleanCondition tree.condition)
      ++ reducedRuntimeBranchFields schema variableValues parentType
          runtimeType inheritedBooleanCondition tree.branches
    else
      []
  termination_by sizeOf tree
  decreasing_by
    cases tree
    simp_all
    omega

  def reducedRuntimeBranchFields
      (schema : Schema) (variableValues : VariableValues)
      (parentType runtimeType : Name)
      (inheritedBooleanCondition : List BooleanLiteral)
      : List (Branch Tree) -> List (Name × ExecutableField)
    | [] => []
    | branch :: rest =>
        branch.body.reducedRuntimeFields schema variableValues
          (branch.condition.parentType parentType) runtimeType
          inheritedBooleanCondition
        ++ reducedRuntimeBranchFields schema variableValues parentType
            runtimeType inheritedBooleanCondition rest
  termination_by branches => sizeOf branches
  decreasing_by
    all_goals
      cases branch
      simp_wf
      omega
end

theorem collectFlatFields_append
    (schema : Schema) (variableValues : VariableValues)
    (executionParentType : Name) (source : ResolverValue ObjectRef)
    (left right : List Selection)
    : collectFlatFields schema variableValues executionParentType source (left ++ right)
      = collectFlatFields schema variableValues executionParentType source left
        ++ collectFlatFields schema variableValues executionParentType source right := by
  induction left with
  | nil => rfl
  | cons selection rest ih =>
      simp [collectFlatFields, ih, List.append_assoc]

theorem collectFlatFields_map_fieldToSelection
    (schema : Schema) (variableValues : VariableValues)
    (executionParentType runtimeType : Name) (ref : ObjectRef)
    (responseName : Name) (fields : List Field)
    : collectFlatFields schema variableValues executionParentType
        (.object runtimeType ref) (fields.map (Field.toSelection responseName))
      = fields.map
          fun field =>
            (responseName, Field.toExecutable field) := by
  induction fields with
  | nil => rfl
  | cons field rest tail_ih =>
      simp [collectFlatFields, collectFlatSelection, Field.toSelection,
        Field.toExecutable, selectionDirectivesAllowBool, tail_ih]

theorem collectFlatFields_reduceTreeFieldGroup
    (schema : Schema) (variableValues : VariableValues)
    (parentType executionParentType runtimeType : Name) (ref : ObjectRef)
    (inheritedBooleanCondition : List BooleanLiteral) (condition : Condition)
    (group : FieldGroup)
    : collectFlatFields schema variableValues executionParentType
        (.object runtimeType ref)
        (reduceTreeFieldGroup schema parentType inheritedBooleanCondition condition group)
      = group.reducedExecutableFields schema parentType
          inheritedBooleanCondition condition := by
  rw [reduceTreeFieldGroup]
  cases hlookup : schema.lookupField parentType group.first.fieldName with
  | none =>
      simpa [hlookup, FieldGroup.reducedExecutableFields, FieldGroup.selections]
        using collectFlatFields_map_fieldToSelection schema variableValues
          executionParentType runtimeType ref group.responseName group.fields
  | some fieldDefinition =>
      simp [hlookup, FieldGroup.reducedExecutableFields, collectFlatFields,
        collectFlatSelection, reduceInScope, selectionDirectivesAllowBool]

theorem collectFlatFields_reduceTreeFieldGroups
    (schema : Schema) (variableValues : VariableValues)
    (parentType executionParentType runtimeType : Name) (ref : ObjectRef)
    (inheritedBooleanCondition : List BooleanLiteral) (condition : Condition)
    (groups : List FieldGroup)
    : collectFlatFields schema variableValues executionParentType
        (.object runtimeType ref)
        (reduceTreeFieldGroups schema parentType inheritedBooleanCondition condition
          groups)
      = groups.flatMap
          (FieldGroup.reducedExecutableFields schema parentType
            inheritedBooleanCondition condition) := by
  induction groups with
  | nil => simp [reduceTreeFieldGroups, collectFlatFields]
  | cons group rest tail_ih =>
      simp [reduceTreeFieldGroups, collectFlatFields_append,
        collectFlatFields_reduceTreeFieldGroup, tail_ih]

theorem collectFlatSelection_branchCondition_toSelection
    (schema : Schema) (variableValues : VariableValues)
    (executionParentType runtimeType : Name) (ref : ObjectRef)
    (condition : BranchCondition) (selectionSet : List Selection)
    : collectFlatSelection schema variableValues executionParentType
        (.object runtimeType ref) (condition.toSelection selectionSet)
      = if condition.allows schema variableValues runtimeType then
          collectFlatFields schema variableValues executionParentType
            (.object runtimeType ref) selectionSet
        else
          [] := by
  cases condition with
  | typeCondition typeName =>
      simp [BranchCondition.toSelection, collectFlatSelection,
        BranchCondition.allows, doesFragmentTypeApplyBool_object,
        selectionDirectivesAllowBool] <;> rfl
  | booleanLiteral literal =>
      cases literal <;>
        simp [BranchCondition.toSelection, collectFlatSelection,
          BranchCondition.allows, BooleanLiteral.toDirective,
          BooleanLiteral.allows, selectionDirectivesAllowBool,
          directiveAllowsSelectionBool] <;> rfl

mutual
  theorem collectFlatFields_reduceTree
      (schema : Schema) (variableValues : VariableValues)
      (parentType executionParentType runtimeType : Name) (ref : ObjectRef)
      (inheritedBooleanCondition : List BooleanLiteral) (tree : Tree)
      (hinherited
        : booleanConditionAllows variableValues inheritedBooleanCondition = true)
      (hcondition : tree.condition.allows variableValues runtimeType = true)
      (hcoherent : tree.BranchesCoherent schema inheritedBooleanCondition)
      : collectFlatFields schema variableValues executionParentType
          (.object runtimeType ref)
          (reduceTree schema parentType inheritedBooleanCondition tree)
        = tree.reducedRuntimeFields schema variableValues parentType
            runtimeType inheritedBooleanCondition := by
    rw [reduceTree, collectFlatFields_append,
      collectFlatFields_reduceTreeFieldGroups]
    rw [Tree.reducedRuntimeFields, if_pos hcondition]
    congr 1
    exact collectFlatFields_reduceTreeBranches schema variableValues parentType
      executionParentType runtimeType ref inheritedBooleanCondition tree.condition
      tree.branches hinherited hcondition
      (by simpa [Tree.BranchesCoherent] using hcoherent)
  termination_by sizeOf tree
  decreasing_by
    cases tree
    simp_all
    omega

  theorem collectFlatFields_reduceTreeBranches
      (schema : Schema) (variableValues : VariableValues)
      (parentType executionParentType runtimeType : Name) (ref : ObjectRef)
      (inheritedBooleanCondition : List BooleanLiteral) (parentCondition : Condition)
      (branches : List (Branch Tree))
      (hinherited
        : booleanConditionAllows variableValues inheritedBooleanCondition = true)
      (hparent : parentCondition.allows variableValues runtimeType = true)
      (hcoherent
        : branchesCoherent schema inheritedBooleanCondition parentCondition branches)
      : collectFlatFields schema variableValues executionParentType
          (.object runtimeType ref)
          (reduceTreeBranches schema parentType inheritedBooleanCondition branches)
        = reducedRuntimeBranchFields schema variableValues parentType
            runtimeType inheritedBooleanCondition branches := by
    cases branches with
    | nil => simp [reduceTreeBranches, collectFlatFields,
        reducedRuntimeBranchFields]
    | cons branch rest =>
        rw [branchesCoherent] at hcoherent
        rw [reduceTreeBranches, collectFlatFields,
          collectFlatSelection_branchCondition_toSelection,
          reducedRuntimeBranchFields]
        have hnext := conditionForBranch?_runtime schema variableValues runtimeType
          inheritedBooleanCondition parentCondition branch.condition hinherited
        rw [hcoherent.1] at hnext
        simp only [conditionOptionAllows] at hnext
        cases hbranch : branch.condition.allows schema variableValues runtimeType with
        | false =>
            have hbodyFalse :
                branch.body.condition.allows variableValues runtimeType = false := by
              simpa [hparent, hbranch] using hnext
            simp only [Bool.false_eq_true, if_false]
            simp only [Tree.reducedRuntimeFields]
            rw [if_neg (by simp [hbodyFalse])]
            simpa using collectFlatFields_reduceTreeBranches schema variableValues
              parentType executionParentType runtimeType ref
              inheritedBooleanCondition parentCondition rest hinherited hparent
              hcoherent.2.2
        | true =>
            have hbodyTrue :
                branch.body.condition.allows variableValues runtimeType = true := by
              simpa [hparent, hbranch] using hnext
            simp only [if_true]
            rw [collectFlatFields_reduceTree schema variableValues
              (branch.condition.parentType parentType) executionParentType runtimeType
              ref inheritedBooleanCondition branch.body hinherited hbodyTrue
              hcoherent.2.1]
            rw [collectFlatFields_reduceTreeBranches schema variableValues parentType
              executionParentType runtimeType ref inheritedBooleanCondition
              parentCondition rest hinherited hparent hcoherent.2.2]
  termination_by sizeOf branches
  decreasing_by
    all_goals
      subst branches
      cases branch
      simp_wf
      omega
end

-----------------------------------------------------------------------------------------
-- Field bundles induced by one reduced boundary
-----------------------------------------------------------------------------------------

inductive ReductionUnit where
  | identity (selectionSet : List Selection)
  | reduce (parentType : Name)
    (inheritedBooleanCondition : List BooleanLiteral)
    (selectionSet : List Selection)

namespace ReductionUnit

def selectionSet : ReductionUnit -> List Selection
  | .identity selectionSet => selectionSet
  | .reduce _ _ selectionSet => selectionSet

def inputSelectionSet (units : List ReductionUnit) : List Selection :=
  units.flatMap ReductionUnit.selectionSet

def outputSelectionSet (schema : Schema) (units : List ReductionUnit) : List Selection :=
  units.flatMap
    fun
    | .identity selectionSet => selectionSet
    | .reduce parentType inheritedBooleanCondition selectionSet =>
        reduceInScope schema parentType inheritedBooleanCondition selectionSet

end ReductionUnit

structure RuntimeFieldBundle where
  responseName : Name
  reducedField : ExecutableField
  sourceFields : List ExecutableField
  childUnit : ReductionUnit

namespace RuntimeFieldBundle

def identity (entry : Name × ExecutableField) : RuntimeFieldBundle :=
  {
    responseName := entry.1
    reducedField := entry.2
    sourceFields := [entry.2]
    childUnit := .identity entry.2.selectionSet
  }

def reduced (schema : Schema)
    (inheritedBooleanCondition : List BooleanLiteral) (condition : Condition)
    (group : FieldGroup) (fieldDefinition : FieldDefinition)
    : RuntimeFieldBundle :=
  let childInheritedBooleanCondition :=
    (canonicalBooleanCondition
      (inheritedBooleanCondition ++ condition.booleanCondition)).getD
      inheritedBooleanCondition
  {
    responseName := group.responseName
    reducedField :=
      {
        fieldName := group.first.fieldName
        arguments := group.first.arguments
        selectionSet :=
          reduceInScope schema fieldDefinition.outputType.namedType
            childInheritedBooleanCondition group.mergedSelectionSet
      }
    sourceFields :=
      group.fields.map Field.toExecutable
    childUnit :=
      .reduce fieldDefinition.outputType.namedType
        childInheritedBooleanCondition group.mergedSelectionSet
  }

def reducedFields (bundles : List RuntimeFieldBundle) : List ExecutableField :=
  bundles.map RuntimeFieldBundle.reducedField

def reducedEntries (bundles : List RuntimeFieldBundle) : List (Name × ExecutableField) :=
  bundles.map fun bundle => (bundle.responseName, bundle.reducedField)

def allSourceFields (bundles : List RuntimeFieldBundle) : List ExecutableField :=
  bundles.flatMap RuntimeFieldBundle.sourceFields

def allSourceEntries (bundles : List RuntimeFieldBundle)
    : List (Name × ExecutableField) :=
  bundles.flatMap
    fun bundle =>
      bundle.sourceFields.map fun field => (bundle.responseName, field)

def allChildUnits (bundles : List RuntimeFieldBundle) : List ReductionUnit :=
  bundles.map RuntimeFieldBundle.childUnit

theorem reducedSelectionSet_eq_outputChildUnits
    (schema : Schema) (bundles : List RuntimeFieldBundle)
    (hvalid
      : ∀ bundle,
          bundle ∈ bundles
          -> bundle.reducedField.selectionSet
              = ReductionUnit.outputSelectionSet schema [bundle.childUnit])
    : (reducedFields bundles).flatMap ExecutableField.selectionSet
      = ReductionUnit.outputSelectionSet schema (allChildUnits bundles) := by
  induction bundles with
  | nil => rfl
  | cons bundle rest ih =>
      simp only [reducedFields, List.map_cons, List.flatMap_cons, allChildUnits,
        ReductionUnit.outputSelectionSet]
      rw [hvalid bundle (by simp)]
      have hrest := ih fun candidate hcandidate =>
        hvalid candidate (by simp [hcandidate])
      simpa [reducedFields, allChildUnits, ReductionUnit.outputSelectionSet]
        using congrArg
          (fun suffix =>
            ReductionUnit.outputSelectionSet schema [bundle.childUnit] ++ suffix)
          hrest

theorem sourceSelectionSet_eq_inputChildUnits
    (bundles : List RuntimeFieldBundle)
    (hvalid
      : ∀ bundle,
          bundle ∈ bundles
          -> bundle.sourceFields.flatMap ExecutableField.selectionSet
              = ReductionUnit.inputSelectionSet [bundle.childUnit])
    : (allSourceFields bundles).flatMap ExecutableField.selectionSet
      = ReductionUnit.inputSelectionSet (allChildUnits bundles) := by
  induction bundles with
  | nil => rfl
  | cons bundle rest ih =>
      simp only [allSourceFields, List.flatMap_cons, List.flatMap_append,
        allChildUnits, List.map_cons, ReductionUnit.inputSelectionSet]
      rw [hvalid bundle (by simp)]
      have hrest := ih fun candidate hcandidate =>
        hvalid candidate (by simp [hcandidate])
      simpa [allSourceFields, allChildUnits, ReductionUnit.inputSelectionSet]
        using congrArg
          (fun suffix =>
            ReductionUnit.inputSelectionSet [bundle.childUnit] ++ suffix)
          hrest

end RuntimeFieldBundle

def FieldGroup.runtimeBundles
    (schema : Schema) (parentType : Name)
    (inheritedBooleanCondition : List BooleanLiteral) (condition : Condition)
    (group : FieldGroup)
    : List RuntimeFieldBundle :=
  match schema.lookupField parentType group.first.fieldName with
  | none =>
      group.fields.map
        fun field =>
          let executable := field.toExecutable
          RuntimeFieldBundle.identity (group.responseName, executable)
  | some fieldDefinition =>
      [RuntimeFieldBundle.reduced schema
        inheritedBooleanCondition condition group fieldDefinition]

mutual
  def Tree.runtimeReductionBundles
      (schema : Schema) (variableValues : VariableValues)
      (parentType runtimeType : Name)
      (inheritedBooleanCondition : List BooleanLiteral) (tree : Tree)
      : List RuntimeFieldBundle :=
    if tree.condition.allows variableValues runtimeType then
      tree.fields.flatMap
        (FieldGroup.runtimeBundles schema parentType
          inheritedBooleanCondition tree.condition)
      ++ runtimeReductionBranchBundles schema variableValues parentType
          runtimeType inheritedBooleanCondition tree.branches
    else
      []
  termination_by sizeOf tree
  decreasing_by
    cases tree
    simp_all
    omega

  def runtimeReductionBranchBundles
      (schema : Schema) (variableValues : VariableValues)
      (parentType runtimeType : Name)
      (inheritedBooleanCondition : List BooleanLiteral)
      : List (Branch Tree) -> List RuntimeFieldBundle
    | [] => []
    | branch :: rest =>
        branch.body.runtimeReductionBundles schema variableValues
          (branch.condition.parentType parentType) runtimeType
          inheritedBooleanCondition
        ++ runtimeReductionBranchBundles schema variableValues parentType
            runtimeType inheritedBooleanCondition rest
  termination_by branches => sizeOf branches
  decreasing_by
    all_goals
      cases branch
      simp_wf
      omega
end

theorem FieldGroup.runtimeBundles_reducedFields
    (schema : Schema) (parentType : Name)
    (inheritedBooleanCondition : List BooleanLiteral) (condition : Condition)
    (group : FieldGroup)
    : RuntimeFieldBundle.reducedEntries
        (group.runtimeBundles schema parentType inheritedBooleanCondition condition)
      = group.reducedExecutableFields schema parentType
          inheritedBooleanCondition condition := by
  unfold FieldGroup.runtimeBundles FieldGroup.reducedExecutableFields
  cases hlookup : schema.lookupField parentType group.first.fieldName with
  | none =>
      simp [RuntimeFieldBundle.reducedEntries, RuntimeFieldBundle.identity]
  | some fieldDefinition =>
      simp [RuntimeFieldBundle.reducedEntries, RuntimeFieldBundle.reduced]

theorem FieldGroup.runtimeBundles_sourceFields
    (schema : Schema) (parentType : Name)
    (inheritedBooleanCondition : List BooleanLiteral) (condition : Condition)
    (group : FieldGroup)
    : RuntimeFieldBundle.allSourceEntries
        (group.runtimeBundles schema parentType inheritedBooleanCondition condition)
      = group.fields.map
          fun field =>
            (group.responseName, Field.toExecutable field) := by
  unfold FieldGroup.runtimeBundles
  cases hlookup : schema.lookupField parentType group.first.fieldName with
  | none =>
      induction group.fields with
      | nil => rfl
      | cons field rest ih =>
          rw [List.map_cons, RuntimeFieldBundle.allSourceEntries, List.flatMap_cons]
          simp [RuntimeFieldBundle.identity]
          exact ih
  | some fieldDefinition =>
      simp [RuntimeFieldBundle.allSourceEntries, RuntimeFieldBundle.reduced]

theorem runtimeBundlesFieldGroups_reducedFields
    (schema : Schema) (parentType : Name)
    (inheritedBooleanCondition : List BooleanLiteral) (condition : Condition)
    (groups : List FieldGroup)
    : RuntimeFieldBundle.reducedEntries
        (groups.flatMap
          fun group =>
            group.runtimeBundles schema parentType inheritedBooleanCondition condition)
      = groups.flatMap
          (FieldGroup.reducedExecutableFields schema parentType
            inheritedBooleanCondition condition) := by
  induction groups with
  | nil => rfl
  | cons group rest ih =>
      rw [List.flatMap_cons, RuntimeFieldBundle.reducedEntries, List.map_append]
      have hgroup := group.runtimeBundles_reducedFields schema parentType
        inheritedBooleanCondition condition
      unfold RuntimeFieldBundle.reducedEntries at hgroup ih
      rw [hgroup, ih]
      rfl

theorem runtimeBundlesFieldGroups_sourceFields
    (schema : Schema) (parentType : Name)
    (inheritedBooleanCondition : List BooleanLiteral) (condition : Condition)
    (groups : List FieldGroup)
    : RuntimeFieldBundle.allSourceEntries
        (groups.flatMap
          fun group =>
            group.runtimeBundles schema parentType inheritedBooleanCondition condition)
      = groups.flatMap
          fun group =>
            group.fields.map
              fun field =>
                (group.responseName, Field.toExecutable field) := by
  induction groups with
  | nil => rfl
  | cons group rest ih =>
      rw [List.flatMap_cons, RuntimeFieldBundle.allSourceEntries,
        List.flatMap_append]
      have hgroup := group.runtimeBundles_sourceFields schema parentType
        inheritedBooleanCondition condition
      unfold RuntimeFieldBundle.allSourceEntries at hgroup ih
      rw [hgroup, ih]
      rfl

mutual
  theorem Tree.runtimeReductionBundles_reducedFields
      (schema : Schema) (variableValues : VariableValues)
      (parentType runtimeType : Name)
      (inheritedBooleanCondition : List BooleanLiteral) (tree : Tree)
      : RuntimeFieldBundle.reducedEntries
          (tree.runtimeReductionBundles schema variableValues parentType
            runtimeType inheritedBooleanCondition)
        = tree.reducedRuntimeFields schema variableValues parentType
            runtimeType inheritedBooleanCondition := by
    rw [Tree.runtimeReductionBundles, Tree.reducedRuntimeFields]
    split
    · rw [RuntimeFieldBundle.reducedEntries, List.map_append]
      have hlocal := runtimeBundlesFieldGroups_reducedFields schema parentType
        inheritedBooleanCondition tree.condition tree.fields
      have hbranches := runtimeReductionBranchBundles_reducedFields schema variableValues
        parentType runtimeType inheritedBooleanCondition
        tree.branches
      unfold RuntimeFieldBundle.reducedEntries at hlocal hbranches
      rw [hlocal, hbranches]
    · rfl
  termination_by sizeOf tree
  decreasing_by
    cases tree
    simp_all
    omega

  theorem runtimeReductionBranchBundles_reducedFields
      (schema : Schema) (variableValues : VariableValues)
      (parentType runtimeType : Name)
      (inheritedBooleanCondition : List BooleanLiteral)
      (branches : List (Branch Tree))
      : RuntimeFieldBundle.reducedEntries
          (runtimeReductionBranchBundles schema variableValues parentType
            runtimeType inheritedBooleanCondition branches)
        = reducedRuntimeBranchFields schema variableValues parentType
            runtimeType inheritedBooleanCondition branches := by
    cases branches with
    | nil => simp [runtimeReductionBranchBundles, reducedRuntimeBranchFields,
        RuntimeFieldBundle.reducedEntries]
    | cons branch rest =>
        rw [runtimeReductionBranchBundles, reducedRuntimeBranchFields,
            RuntimeFieldBundle.reducedEntries, List.map_append]
        have hbody := branch.body.runtimeReductionBundles_reducedFields schema
          variableValues (branch.condition.parentType parentType)
          runtimeType inheritedBooleanCondition
        have hrest := runtimeReductionBranchBundles_reducedFields schema variableValues
          parentType runtimeType inheritedBooleanCondition rest
        unfold RuntimeFieldBundle.reducedEntries at hbody hrest
        rw [hbody, hrest]
  termination_by sizeOf branches
  decreasing_by
    all_goals
      subst branches
      cases branch
      simp_wf
      omega
end

theorem runtimeFieldsForEntries_append
    (variableValues : VariableValues) (runtimeType : Name)
    (left right : List (Condition × NamedField))
    : runtimeFieldsForEntries variableValues runtimeType (left ++ right)
      = runtimeFieldsForEntries variableValues runtimeType left
        ++ runtimeFieldsForEntries variableValues runtimeType right := by
  induction left with
  | nil => rfl
  | cons entry rest ih =>
      simp [runtimeFieldsForEntries, List.append_assoc]

theorem runtimeFieldsForEntries_group
    (variableValues : VariableValues) (runtimeType : Name)
    (condition : Condition) (group : FieldGroup)
    : runtimeFieldsForEntries variableValues runtimeType
        (group.fields.map
          fun field =>
            (condition, ({ responseName := group.responseName, field } : NamedField)))
      = if condition.allows variableValues runtimeType then
          group.fields.map
            fun field =>
              (group.responseName, Field.toExecutable field)
        else
          [] := by
  induction group.fields with
  | nil => simp [runtimeFieldsForEntries]
  | cons field rest ih =>
      unfold runtimeFieldsForEntries at ih
      cases hallows : condition.allows variableValues runtimeType <;>
        simp [runtimeFieldsForEntries, Field.toExecutable, hallows, ih]

theorem runtimeFieldsForEntries_groups
    (variableValues : VariableValues) (runtimeType : Name)
    (condition : Condition) (groups : List FieldGroup)
    : runtimeFieldsForEntries variableValues runtimeType
        (groups.flatMap
          fun group =>
            group.fields.map
              fun field =>
                (condition, ({ responseName := group.responseName, field } : NamedField)))
      = if condition.allows variableValues runtimeType then
          groups.flatMap
            fun group =>
              group.fields.map
                fun field =>
                  (group.responseName, Field.toExecutable field)
        else
          [] := by
  induction groups with
  | nil => simp [runtimeFieldsForEntries]
  | cons group rest ih =>
      rw [List.flatMap_cons, runtimeFieldsForEntries_append,
        runtimeFieldsForEntries_group, ih]
      cases hallows : condition.allows variableValues runtimeType <;> simp

theorem Tree.branches_sizeOf_lt (tree : Tree) : sizeOf tree.branches < sizeOf tree := by
  cases tree
  simp_all
  omega

mutual
  theorem Tree.runtimeReductionBundles_sourceFields
      (schema : Schema) (variableValues : VariableValues)
      (parentType runtimeType : Name)
      (inheritedBooleanCondition : List BooleanLiteral) (tree : Tree)
      (hinherited
        : booleanConditionAllows variableValues inheritedBooleanCondition = true)
      (hcoherent : tree.BranchesCoherent schema inheritedBooleanCondition)
      : RuntimeFieldBundle.allSourceEntries
          (tree.runtimeReductionBundles schema variableValues parentType
            runtimeType inheritedBooleanCondition)
        = tree.collectRuntimeFields variableValues runtimeType := by
    rw [Tree.runtimeReductionBundles]
    split
    · rename_i hallows
      rw [RuntimeFieldBundle.allSourceEntries, List.flatMap_append]
      have hlocal := runtimeBundlesFieldGroups_sourceFields schema parentType
        inheritedBooleanCondition tree.condition tree.fields
      unfold RuntimeFieldBundle.allSourceEntries at hlocal
      rw [hlocal]
      rw [Tree.collectRuntimeFields, Tree.storedFieldEntries,
        runtimeFieldsForEntries_append,
        runtimeFieldsForEntries_groups]
      rw [if_pos hallows]
      have hbranches := runtimeReductionBranchBundles_sourceFields schema
        variableValues parentType runtimeType
        inheritedBooleanCondition tree.condition tree.branches hinherited
        (by simpa [Tree.BranchesCoherent] using hcoherent)
      unfold RuntimeFieldBundle.allSourceEntries at hbranches
      rw [hbranches]
    · rename_i hnot
      rw [Tree.collectRuntimeFields, Tree.storedFieldEntries,
        runtimeFieldsForEntries_append,
        runtimeFieldsForEntries_groups]
      have hfalse : tree.condition.allows variableValues runtimeType = false := by
        cases hvalue : tree.condition.allows variableValues runtimeType
        · rfl
        · exact False.elim (hnot hvalue)
      rw [if_neg (by simpa using hfalse)]
      have hbranches := runtimeFieldsForEntries_branches_false schema
        variableValues parentType runtimeType
        inheritedBooleanCondition tree.condition tree.branches hinherited hfalse
        (by simpa [Tree.BranchesCoherent] using hcoherent)
      rw [hbranches]
      simp [RuntimeFieldBundle.allSourceEntries]
  termination_by sizeOf tree
  decreasing_by
    simp_wf
    all_goals exact Tree.branches_sizeOf_lt tree

  theorem runtimeReductionBranchBundles_sourceFields
      (schema : Schema) (variableValues : VariableValues)
      (parentType runtimeType : Name)
      (inheritedBooleanCondition : List BooleanLiteral)
      (parentCondition : Condition)
      (branches : List (Branch Tree))
      (hinherited
        : booleanConditionAllows variableValues inheritedBooleanCondition = true)
      (hcoherent
        : branchesCoherent schema inheritedBooleanCondition parentCondition branches)
      : RuntimeFieldBundle.allSourceEntries
          (runtimeReductionBranchBundles schema variableValues parentType
            runtimeType inheritedBooleanCondition branches)
        = runtimeFieldsForEntries variableValues runtimeType
            (branchStoredFieldEntries branches) := by
    cases branches with
    | nil => simp [RuntimeFieldBundle.allSourceEntries,
        runtimeReductionBranchBundles, branchStoredFieldEntries,
        runtimeFieldsForEntries]
    | cons branch rest =>
        rw [branchesCoherent] at hcoherent
        rw [runtimeReductionBranchBundles, branchStoredFieldEntries,
          RuntimeFieldBundle.allSourceEntries, List.flatMap_append,
          runtimeFieldsForEntries_append]
        have hbody := branch.body.runtimeReductionBundles_sourceFields schema
          variableValues (branch.condition.parentType parentType)
          runtimeType inheritedBooleanCondition hinherited hcoherent.2.1
        have hrest := runtimeReductionBranchBundles_sourceFields schema variableValues
          parentType runtimeType inheritedBooleanCondition
          parentCondition rest hinherited hcoherent.2.2
        unfold RuntimeFieldBundle.allSourceEntries at hbody hrest
        unfold Tree.collectRuntimeFields at hbody
        rw [hbody, hrest]
  termination_by sizeOf branches
  decreasing_by
    all_goals
      subst branches
      cases branch
      simp_wf
      omega

  theorem runtimeFieldsForEntries_branches_false
      (schema : Schema) (variableValues : VariableValues)
      (parentType runtimeType : Name)
      (inheritedBooleanCondition : List BooleanLiteral)
      (parentCondition : Condition) (branches : List (Branch Tree))
      (hinherited
        : booleanConditionAllows variableValues inheritedBooleanCondition = true)
      (hparent : parentCondition.allows variableValues runtimeType = false)
      (hcoherent
        : branchesCoherent schema inheritedBooleanCondition parentCondition branches)
      : runtimeFieldsForEntries variableValues runtimeType
          (branchStoredFieldEntries branches)
        = [] := by
    cases branches with
    | nil => simp [branchStoredFieldEntries, runtimeFieldsForEntries]
    | cons branch rest =>
        rw [branchesCoherent] at hcoherent
        have hnext := conditionForBranch?_runtime schema variableValues runtimeType
          inheritedBooleanCondition parentCondition branch.condition hinherited
        rw [hcoherent.1] at hnext
        simp only [conditionOptionAllows] at hnext
        have hbodyFalse :
            branch.body.condition.allows variableValues runtimeType = false := by
          cases hbranch : branch.condition.allows schema variableValues runtimeType <;>
            simpa [hparent, hbranch] using hnext
        have hbody := branch.body.runtimeReductionBundles_sourceFields schema
          variableValues (branch.condition.parentType parentType)
          runtimeType inheritedBooleanCondition hinherited hcoherent.2.1
        rw [Tree.runtimeReductionBundles, if_neg (by simpa using hbodyFalse),
          RuntimeFieldBundle.allSourceEntries] at hbody
        have hrest := runtimeFieldsForEntries_branches_false schema variableValues
          parentType runtimeType inheritedBooleanCondition
          parentCondition rest hinherited hparent hcoherent.2.2
        rw [branchStoredFieldEntries, runtimeFieldsForEntries_append]
        unfold Tree.collectRuntimeFields at hbody
        have hbodyNil :
            runtimeFieldsForEntries variableValues runtimeType
              branch.body.storedFieldEntries = [] := by
          simpa [RuntimeFieldBundle.allSourceEntries] using hbody.symm
        rw [hbodyNil, hrest, List.nil_append]
  termination_by sizeOf branches
  decreasing_by
    all_goals
      subst branches
      cases branch
      simp_wf
      omega

end

-----------------------------------------------------------------------------------------
-- Generic bundle grouping
-----------------------------------------------------------------------------------------

structure RuntimeFieldBundle.WellFormed (schema : Schema) (bundle : RuntimeFieldBundle)
    : Prop where
  sourceNonempty : bundle.sourceFields ≠ []
  representative
    : ∃ field,
        field ∈ bundle.sourceFields
        ∧ field.fieldName = bundle.reducedField.fieldName
        ∧ field.arguments = bundle.reducedField.arguments
  reducedChildren
    : bundle.reducedField.selectionSet
      = ReductionUnit.outputSelectionSet schema [bundle.childUnit]
  sourceChildren
    : bundle.sourceFields.flatMap ExecutableField.selectionSet
      = ReductionUnit.inputSelectionSet [bundle.childUnit]

theorem RuntimeFieldBundle.identity_wellFormed
    (schema : Schema) (entry : Name × ExecutableField)
    : (RuntimeFieldBundle.identity entry).WellFormed schema := by
  constructor
  · simp [RuntimeFieldBundle.identity]
  · exact ⟨entry.2, by simp [RuntimeFieldBundle.identity]⟩
  · simp [RuntimeFieldBundle.identity, ReductionUnit.outputSelectionSet]
  · simp [RuntimeFieldBundle.identity, ReductionUnit.inputSelectionSet,
      ReductionUnit.selectionSet]

theorem RuntimeFieldBundle.reduced_wellFormed
    (schema : Schema)
    (inheritedBooleanCondition : List BooleanLiteral) (condition : Condition)
    (group : FieldGroup) (fieldDefinition : FieldDefinition)
    : (RuntimeFieldBundle.reduced schema
        inheritedBooleanCondition condition group fieldDefinition).WellFormed
        schema := by
  constructor
  · simp [RuntimeFieldBundle.reduced, FieldGroup.fields]
  · exact ⟨Field.toExecutable group.first,
      by simp [RuntimeFieldBundle.reduced, FieldGroup.fields, Field.toExecutable]⟩
  · simp [RuntimeFieldBundle.reduced, ReductionUnit.outputSelectionSet]
  · have hchildren :
        (group.fields.map
            Field.toExecutable).flatMap
            ExecutableField.selectionSet
          = group.fields.flatMap Field.selectionSet := by
      induction group.fields with
      | nil => rfl
      | cons field rest ih =>
          simp [Field.toExecutable, ih]
    have hmerge : ∀ fields : List Field,
        SelectionSet.mergeSelectionSets
            (fields.map (Field.toSelection group.responseName))
          = fields.flatMap Field.selectionSet := by
      intro fields
      induction fields with
      | nil => rfl
      | cons field rest ih =>
          rw [show
            (field :: rest).map (Field.toSelection group.responseName)
              = [field.toSelection group.responseName]
                ++ rest.map (Field.toSelection group.responseName) by rfl]
          rw [Termination.mergeSelectionSets_append, List.flatMap_cons]
          have hsingle : SelectionSet.mergeSelectionSets
              [field.toSelection group.responseName] = field.selectionSet := by
            simp [SelectionSet.mergeSelectionSets, Field.toSelection,
              Selection.subselections]
          rw [hsingle, ih]
    have hmerged : group.mergedSelectionSet
        = group.fields.flatMap Field.selectionSet := by
      exact hmerge group.fields
    simpa [RuntimeFieldBundle.reduced, ReductionUnit.inputSelectionSet,
      ReductionUnit.selectionSet, hmerged]
      using hchildren

-- Stable insertion into a list-backed map whose values are accumulated lists.
-- This generic helper belongs to reduction proof machinery rather than the
-- spec-facing execution model.
def addNameGroup {Entry : Type} (group : Name × List Entry)
    : List (Name × List Entry) -> List (Name × List Entry)
  | [] => [group]
  | (name, entries) :: rest =>
      if name == group.fst then
        (name, entries ++ group.snd) :: rest
      else
        (name, entries) :: addNameGroup group rest

def addRuntimeFieldBundleGroup (group : Name × List RuntimeFieldBundle)
    : List (Name × List RuntimeFieldBundle) -> List (Name × List RuntimeFieldBundle) :=
  addNameGroup group

def groupRuntimeFieldBundles (bundles : List RuntimeFieldBundle)
    : List (Name × List RuntimeFieldBundle) :=
  bundles.foldl
    (fun groups bundle =>
      addRuntimeFieldBundleGroup (bundle.responseName, [bundle]) groups)
    []

def RuntimeFieldBundleGroupsKeyed (groups : List (Name × List RuntimeFieldBundle))
    : Prop :=
  ∀ responseName bundles,
    (responseName, bundles) ∈ groups
    -> ∀ bundle, bundle ∈ bundles -> bundle.responseName = responseName

theorem RuntimeFieldBundleGroupsKeyed.add
    (bundle : RuntimeFieldBundle)
    (groups : List (Name × List RuntimeFieldBundle))
    (hgroups : RuntimeFieldBundleGroupsKeyed groups)
    : RuntimeFieldBundleGroupsKeyed
        (addRuntimeFieldBundleGroup (bundle.responseName, [bundle]) groups) := by
  induction groups with
  | nil =>
      simp [RuntimeFieldBundleGroupsKeyed, addRuntimeFieldBundleGroup, addNameGroup]
  | cons group rest ih =>
      rcases group with ⟨name, entries⟩
      simp only [addRuntimeFieldBundleGroup, addNameGroup]
      split
      · rename_i heq
        have hname : name = bundle.responseName := beq_iff_eq.mp heq
        intro candidateName candidateBundles hmember candidate hcandidate
        rcases List.mem_cons.mp hmember with hhead | htail
        · cases hhead
          rcases List.mem_append.mp hcandidate with hcurrent | hnew
          · exact hgroups name entries (by simp) candidate hcurrent
          · have : candidate = bundle := by simpa using hnew
            subst candidate
            exact hname.symm
        · exact hgroups candidateName candidateBundles (by simp [htail])
            candidate hcandidate
      · intro candidateName candidateBundles hmember candidate hcandidate
        rcases List.mem_cons.mp hmember with hhead | htail
        · cases hhead
          exact hgroups name entries (by simp) candidate hcandidate
        · apply ih
          · intro tailName tailBundles htailGroup tailBundle htailBundle
            exact hgroups tailName tailBundles (by simp [htailGroup])
              tailBundle htailBundle
          · exact htail
          · exact hcandidate

theorem groupRuntimeFieldBundles_keyed (bundles : List RuntimeFieldBundle)
    : RuntimeFieldBundleGroupsKeyed (groupRuntimeFieldBundles bundles) := by
  unfold groupRuntimeFieldBundles
  have hgeneral : ∀ (rest : List RuntimeFieldBundle)
      (groups : List (Name × List RuntimeFieldBundle)),
      RuntimeFieldBundleGroupsKeyed groups ->
      RuntimeFieldBundleGroupsKeyed
        (rest.foldl
          (fun groups bundle =>
            addRuntimeFieldBundleGroup (bundle.responseName, [bundle]) groups)
          groups) := by
    intro rest
    induction rest with
    | nil => exact fun groups hgroups => hgroups
    | cons bundle tail ih =>
        intro groups hgroups
        exact ih _ (RuntimeFieldBundleGroupsKeyed.add bundle groups hgroups)
  exact hgeneral bundles [] (by simp [RuntimeFieldBundleGroupsKeyed])

def reducedBundleGroups (groups : List (Name × List RuntimeFieldBundle))
    : List (Name × List ExecutableField) :=
  groups.map fun group => (group.1, group.2.map RuntimeFieldBundle.reducedField)

def sourceBundleGroups (groups : List (Name × List RuntimeFieldBundle))
    : List (Name × List ExecutableField) :=
  groups.map fun group => (group.1, group.2.flatMap RuntimeFieldBundle.sourceFields)

def flattenRuntimeFieldBundleGroups
    : List (Name × List RuntimeFieldBundle) -> List RuntimeFieldBundle
  | [] => []
  | group :: rest => group.2 ++ flattenRuntimeFieldBundleGroups rest

theorem reducedBundleGroups_add_singleton
    (bundle : RuntimeFieldBundle)
    (groups : List (Name × List RuntimeFieldBundle))
    : reducedBundleGroups
        (addRuntimeFieldBundleGroup (bundle.responseName, [bundle]) groups)
      = addExecutableGroup
          (bundle.responseName, [bundle.reducedField])
          (reducedBundleGroups groups) := by
  induction groups with
  | nil => rfl
  | cons group rest ih =>
      rcases group with ⟨responseName, bundles⟩
      simp only [addRuntimeFieldBundleGroup, addNameGroup, reducedBundleGroups,
        addExecutableGroup, List.map_cons] at ih ⊢
      split <;> simp_all

theorem reducedBundleGroups_foldl
    (bundles : List RuntimeFieldBundle)
    (groups : List (Name × List RuntimeFieldBundle))
    : reducedBundleGroups
        (bundles.foldl
          (fun groups bundle =>
            addRuntimeFieldBundleGroup (bundle.responseName, [bundle]) groups)
          groups)
      = bundles.foldl
          (fun groups bundle =>
            addExecutableGroup (bundle.responseName, [bundle.reducedField]) groups)
          (reducedBundleGroups groups) := by
  induction bundles generalizing groups with
  | nil => rfl
  | cons bundle rest ih =>
      simp only [List.foldl_cons]
      rw [ih, reducedBundleGroups_add_singleton]

theorem reducedBundleGroups_groupRuntimeFieldBundles (bundles : List RuntimeFieldBundle)
    : reducedBundleGroups (groupRuntimeFieldBundles bundles)
      = groupExecutableFields (RuntimeFieldBundle.reducedEntries bundles) := by
  rw [groupRuntimeFieldBundles, reducedBundleGroups_foldl]
  unfold groupExecutableFields RuntimeFieldBundle.reducedEntries
  rw [List.foldl_map]
  rfl

theorem flattenRuntimeFieldBundleGroups_add_perm
    (group : Name × List RuntimeFieldBundle)
    (groups : List (Name × List RuntimeFieldBundle))
    : (flattenRuntimeFieldBundleGroups (addRuntimeFieldBundleGroup group groups)).Perm
        (flattenRuntimeFieldBundleGroups groups ++ group.2) := by
  induction groups with
  | nil => simp [addRuntimeFieldBundleGroup, addNameGroup,
      flattenRuntimeFieldBundleGroups]
  | cons current rest ih =>
      rcases current with ⟨responseName, bundles⟩
      rcases group with ⟨groupName, groupBundles⟩
      simp only [addRuntimeFieldBundleGroup, addNameGroup] at ih ⊢
      split
      · simpa [flattenRuntimeFieldBundleGroups, List.append_assoc]
          using List.Perm.append_left bundles
            (List.perm_append_comm (l₁ := groupBundles)
              (l₂ := flattenRuntimeFieldBundleGroups rest))
      · simpa [flattenRuntimeFieldBundleGroups, List.append_assoc]
          using List.Perm.append_left bundles ih

theorem flattenRuntimeFieldBundleGroups_foldl_perm
    (bundles : List RuntimeFieldBundle)
    (groups : List (Name × List RuntimeFieldBundle))
    : (flattenRuntimeFieldBundleGroups
        (bundles.foldl
          (fun groups bundle =>
            addRuntimeFieldBundleGroup (bundle.responseName, [bundle]) groups)
          groups)).Perm
        (flattenRuntimeFieldBundleGroups groups ++ bundles) := by
  induction bundles generalizing groups with
  | nil => simp
  | cons bundle rest ih =>
      simp only [List.foldl_cons]
      have htail := ih
        (addRuntimeFieldBundleGroup
          (bundle.responseName, [bundle]) groups)
      exact htail.trans <| by
        have hadd := flattenRuntimeFieldBundleGroups_add_perm
          (bundle.responseName, [bundle]) groups
        exact (hadd.append_right rest).trans (by simp [List.append_assoc])

theorem flattenRuntimeFieldBundleGroups_group_perm (bundles : List RuntimeFieldBundle)
    : (flattenRuntimeFieldBundleGroups (groupRuntimeFieldBundles bundles)).Perm
        bundles := by
  simpa [groupRuntimeFieldBundles, flattenRuntimeFieldBundleGroups]
    using flattenRuntimeFieldBundleGroups_foldl_perm bundles []

theorem flatten_sourceBundleGroups
    (groups : List (Name × List RuntimeFieldBundle))
    (hkeyed
      : ∀ responseName bundles,
          (responseName, bundles) ∈ groups
          -> ∀ bundle, bundle ∈ bundles -> bundle.responseName = responseName)
    : flattenExecutableFieldGroups (sourceBundleGroups groups)
      = (flattenRuntimeFieldBundleGroups groups).flatMap
          (fun bundle =>
            bundle.sourceFields.map fun field => (bundle.responseName, field)) := by
  induction groups with
  | nil => rfl
  | cons group rest ih =>
      rcases group with ⟨responseName, bundles⟩
      have hnames : ∀ bundle, bundle ∈ bundles -> bundle.responseName = responseName := by
        intro bundle hbundle
        exact hkeyed responseName bundles (by simp) bundle hbundle
      have htail : ∀ name tailBundles,
          (name, tailBundles) ∈ rest ->
          ∀ bundle, bundle ∈ tailBundles -> bundle.responseName = name := by
        intro name tailBundles hgroup bundle hbundle
        exact hkeyed name tailBundles (by simp [hgroup]) bundle hbundle
      have hlocalGeneral : ∀ current : List RuntimeFieldBundle,
          (∀ bundle, bundle ∈ current -> bundle.responseName = responseName) ->
          (current.flatMap fun bundle =>
              bundle.sourceFields.map fun field => (responseName, field))
            = current.flatMap fun bundle =>
                bundle.sourceFields.map fun field => (bundle.responseName, field) := by
        intro current hcurrent
        induction current with
        | nil => rfl
        | cons bundle tail tail_ih =>
            rw [List.flatMap_cons, List.flatMap_cons,
              hcurrent bundle (by simp)]
            exact congrArg
              (fun suffix =>
                bundle.sourceFields.map (fun field => (responseName, field)) ++ suffix)
              (tail_ih
                fun candidate hcandidate =>
                  hcurrent candidate (by simp [hcandidate]))
      have hlocal := hlocalGeneral bundles hnames
      have htailEq := ih htail
      simp only [sourceBundleGroups] at htailEq
      simp only [sourceBundleGroups, List.map_cons,
        flattenExecutableFieldGroups, flattenRuntimeFieldBundleGroups,
        List.map_flatMap]
      rw [hlocal, htailEq, List.flatMap_append]

theorem flatten_sourceBundleGroups_group_perm (bundles : List RuntimeFieldBundle)
    : (flattenExecutableFieldGroups
        (sourceBundleGroups (groupRuntimeFieldBundles bundles))).Perm
        (RuntimeFieldBundle.allSourceEntries bundles) := by
  rw [flatten_sourceBundleGroups _ (groupRuntimeFieldBundles_keyed bundles)]
  unfold RuntimeFieldBundle.allSourceEntries
  exact List.Perm.flatMap
    (flattenRuntimeFieldBundleGroups_group_perm bundles)
    (fun bundle =>
      bundle.sourceFields.map fun field => (bundle.responseName, field))

def RuntimeFieldBundle.GroupsWellFormed (schema : Schema)
    (groups : List (Name × List RuntimeFieldBundle))
    : Prop :=
  ∀ bundle, bundle ∈ flattenRuntimeFieldBundleGroups groups -> bundle.WellFormed schema

theorem mem_flattenRuntimeFieldBundleGroups
    {bundle : RuntimeFieldBundle} {responseName : Name}
    {bundles : List RuntimeFieldBundle}
    {groups : List (Name × List RuntimeFieldBundle)}
    (hgroup : (responseName, bundles) ∈ groups) (hbundle : bundle ∈ bundles)
    : bundle ∈ flattenRuntimeFieldBundleGroups groups := by
  induction groups with
  | nil => simp at hgroup
  | cons group rest ih =>
      rcases List.mem_cons.mp hgroup with hhead | htail
      · subst group
        simp [flattenRuntimeFieldBundleGroups, hbundle]
      · simp only [flattenRuntimeFieldBundleGroups, List.mem_append]
        exact Or.inr (ih htail)

theorem RuntimeFieldBundle.groupsWellFormed_of_group
    (schema : Schema) (bundles : List RuntimeFieldBundle)
    (hbundles : ∀ bundle, bundle ∈ bundles -> bundle.WellFormed schema)
    : RuntimeFieldBundle.GroupsWellFormed schema (groupRuntimeFieldBundles bundles) := by
  intro bundle hbundle
  exact hbundles bundle
    ((flattenRuntimeFieldBundleGroups_group_perm bundles).mem_iff.mp hbundle)

theorem reducedBundleGroups_group_wellFormed (bundles : List RuntimeFieldBundle)
    : NormalForm.executableGroupsWellFormed
        (reducedBundleGroups (groupRuntimeFieldBundles bundles)) := by
  rw [reducedBundleGroups_groupRuntimeFieldBundles]
  exact groupExecutableFields_wellFormed _

theorem sourceBundleGroups_keys (groups : List (Name × List RuntimeFieldBundle))
    : (sourceBundleGroups groups).map Prod.fst
      = (reducedBundleGroups groups).map Prod.fst := by
  induction groups with
  | nil => rfl
  | cons group rest ih =>
      rcases group with ⟨responseName, bundles⟩
      simp [sourceBundleGroups, reducedBundleGroups]

theorem sourceBundleGroups_group_wellFormed
    (schema : Schema) (bundles : List RuntimeFieldBundle)
    (hbundles : ∀ bundle, bundle ∈ bundles -> bundle.WellFormed schema)
    : NormalForm.executableGroupsWellFormed
        (sourceBundleGroups (groupRuntimeFieldBundles bundles)) := by
  let groups := groupRuntimeFieldBundles bundles
  have hgroupBundles : RuntimeFieldBundle.GroupsWellFormed schema groups := by
    exact RuntimeFieldBundle.groupsWellFormed_of_group schema bundles hbundles
  have hreduced := reducedBundleGroups_group_wellFormed bundles
  intro sourceGroup hsourceGroup
  rcases List.mem_map.mp hsourceGroup with ⟨bundleGroup, hbundleGroup, rfl⟩
  rcases bundleGroup with ⟨responseName, groupBundles⟩
  have hreducedGroup :
      (responseName, groupBundles.map RuntimeFieldBundle.reducedField)
        ∈ reducedBundleGroups groups := by
    exact List.mem_map.mpr ⟨(responseName, groupBundles), hbundleGroup, rfl⟩
  have hreducedProperties := hreduced _ hreducedGroup
  cases groupBundles with
  | nil => exact False.elim (hreducedProperties rfl)
  | cons bundle rest =>
      have hbundle := hgroupBundles bundle
        (mem_flattenRuntimeFieldBundleGroups hbundleGroup (by simp))
      intro hempty
      exact hbundle.sourceNonempty (List.append_eq_nil_iff.mp hempty).1

theorem sourceBundleGroups_group_keysNodup (bundles : List RuntimeFieldBundle)
    : ((sourceBundleGroups (groupRuntimeFieldBundles bundles)).map Prod.fst).Nodup := by
  rw [sourceBundleGroups_keys]
  rw [reducedBundleGroups_groupRuntimeFieldBundles]
  exact (groupExecutableFields_exact
    (RuntimeFieldBundle.reducedEntries bundles)).1

-----------------------------------------------------------------------------------------
-- Runtime bundles for reduction units
-----------------------------------------------------------------------------------------

def ReductionUnit.RuntimeApplicable
    (schema : Schema) (variableValues : VariableValues) (runtimeType : Name)
    (unit : ReductionUnit)
    : Prop :=
  match unit with
  | .identity _ => True
  | .reduce parentType inheritedBooleanCondition _ =>
      booleanConditionAllows variableValues inheritedBooleanCondition = true
      ∧ (schema.getPossibleTypes parentType).contains runtimeType = true

def ReductionUnit.runtimeBundles
    (schema : Schema) (variableValues : VariableValues)
    (executionParentType runtimeType : Name) (ref : ObjectRef)
    (unit : ReductionUnit)
    : List RuntimeFieldBundle :=
  match unit with
  | .reduce parentType inheritedBooleanCondition selectionSet =>
      let tree :=
        ofSelectionSetInScope schema parentType inheritedBooleanCondition selectionSet
      tree.runtimeReductionBundles schema variableValues parentType
        runtimeType inheritedBooleanCondition
  | .identity selectionSet =>
      (collectFlatFields schema variableValues executionParentType
        (.object runtimeType ref) selectionSet).map
        RuntimeFieldBundle.identity

def ReductionUnit.runtimeBundlesFor
    (schema : Schema) (variableValues : VariableValues)
    (executionParentType runtimeType : Name) (ref : ObjectRef)
    (units : List ReductionUnit)
    : List RuntimeFieldBundle :=
  units.flatMap
    (ReductionUnit.runtimeBundles schema variableValues executionParentType
      runtimeType ref)

theorem RuntimeFieldBundle.reducedEntries_map_identity
    (entries : List (Name × ExecutableField))
    : RuntimeFieldBundle.reducedEntries (entries.map RuntimeFieldBundle.identity)
      = entries := by
  simp [RuntimeFieldBundle.reducedEntries, RuntimeFieldBundle.identity,
    Function.comp_def]

theorem RuntimeFieldBundle.allSourceEntries_map_identity
    (entries : List (Name × ExecutableField))
    : RuntimeFieldBundle.allSourceEntries (entries.map RuntimeFieldBundle.identity)
      = entries := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
      rw [List.map_cons, RuntimeFieldBundle.allSourceEntries, List.flatMap_cons]
      simp [RuntimeFieldBundle.identity]
      exact ih

theorem ofSelectionSetInScope_condition
    (schema : Schema) (parentType : Name)
    (inheritedBooleanCondition : List BooleanLiteral)
    (selectionSet : List Selection)
    : (ofSelectionSetInScope schema parentType inheritedBooleanCondition
        selectionSet).condition
      = rootCondition schema parentType := by
  unfold ofSelectionSetInScope
  rw [Tree.insertSelections_condition]
  rfl

theorem ReductionUnit.collectFlatFields_output_eq_reducedFields
    (schema : Schema) (variableValues : VariableValues)
    (executionParentType runtimeType : Name) (ref : ObjectRef)
    (unit : ReductionUnit)
    (happlicable : unit.RuntimeApplicable schema variableValues runtimeType)
    : collectFlatFields schema variableValues executionParentType
        (.object runtimeType ref)
        (match unit with
          | .identity selectionSet => selectionSet
          | .reduce parentType inheritedBooleanCondition selectionSet =>
              reduceInScope schema parentType inheritedBooleanCondition selectionSet)
      = RuntimeFieldBundle.reducedEntries
          (unit.runtimeBundles schema variableValues executionParentType
            runtimeType ref) := by
  cases unit with
  | identity selectionSet =>
      exact (RuntimeFieldBundle.reducedEntries_map_identity
        (collectFlatFields schema variableValues executionParentType
          (.object runtimeType ref) selectionSet)).symm
  | reduce parentType inheritedBooleanCondition selectionSet =>
      simp only [ReductionUnit.RuntimeApplicable] at happlicable
      let tree := ofSelectionSetInScope schema parentType
        inheritedBooleanCondition selectionSet
      have hcondition : tree.condition.allows variableValues runtimeType = true := by
        rw [show tree.condition = rootCondition schema parentType by
          exact ofSelectionSetInScope_condition schema parentType
            inheritedBooleanCondition selectionSet]
        unfold Condition.allows rootCondition
        rw [happlicable.2]
        rfl
      have hcollected := collectFlatFields_reduceTree schema variableValues
        parentType executionParentType runtimeType ref inheritedBooleanCondition tree
        happlicable.1 hcondition
        (ofSelectionSetInScope_branchesCoherent schema parentType
          inheritedBooleanCondition selectionSet)
      have hbundles := tree.runtimeReductionBundles_reducedFields schema
        variableValues parentType runtimeType inheritedBooleanCondition
      simpa [ReductionUnit.runtimeBundles, reduceInScope, tree]
        using hcollected.trans hbundles.symm

theorem ReductionUnit.allSourceFields_runtimeBundles_perm
    (schema : Schema) (variableValues : VariableValues)
    (executionParentType runtimeType : Name) (ref : ObjectRef)
    (unit : ReductionUnit)
    (happlicable : unit.RuntimeApplicable schema variableValues runtimeType)
    : (RuntimeFieldBundle.allSourceEntries
        (unit.runtimeBundles schema variableValues executionParentType
          runtimeType ref)).Perm
        (collectFlatFields schema variableValues executionParentType
          (.object runtimeType ref) unit.selectionSet) := by
  cases unit with
  | reduce parentType inheritedBooleanCondition selectionSet =>
      simp only [ReductionUnit.RuntimeApplicable] at happlicable
      let tree := ofSelectionSetInScope schema parentType
        inheritedBooleanCondition selectionSet
      have hsource := tree.runtimeReductionBundles_sourceFields schema variableValues
        parentType runtimeType inheritedBooleanCondition
        happlicable.1
        (ofSelectionSetInScope_branchesCoherent schema parentType
          inheritedBooleanCondition selectionSet)
      have hextracted := extraction_runtimeFields_perm schema parentType
        inheritedBooleanCondition selectionSet variableValues
        executionParentType runtimeType ref happlicable.1 happlicable.2
      have hflat := RuntimeExtraction.collectFlatFields_perm_flatten_collectFields schema
        variableValues
        executionParentType (.object runtimeType ref) selectionSet
      simp only [ReductionUnit.runtimeBundles]
      rw [hsource]
      exact hextracted.trans hflat.symm
  | identity selectionSet =>
      exact List.Perm.of_eq
        (RuntimeFieldBundle.allSourceEntries_map_identity
          (collectFlatFields schema variableValues executionParentType
            (.object runtimeType ref) selectionSet))

theorem FieldGroup.runtimeBundles_wellFormed
    (schema : Schema) (parentType : Name)
    (inheritedBooleanCondition : List BooleanLiteral) (condition : Condition)
    (group : FieldGroup)
    : ∀ bundle,
        bundle
          ∈ group.runtimeBundles schema parentType inheritedBooleanCondition condition
        -> bundle.WellFormed schema := by
  intro bundle hbundle
  unfold FieldGroup.runtimeBundles at hbundle
  split at hbundle
  · rcases List.mem_map.mp hbundle with ⟨field, _hfield, rfl⟩
    exact RuntimeFieldBundle.identity_wellFormed schema
      (group.responseName,
        Field.toExecutable field)
  · rename_i fieldDefinition hlookup
    have : bundle = RuntimeFieldBundle.reduced schema
        inheritedBooleanCondition condition group fieldDefinition := by
      simpa using List.mem_singleton.mp hbundle
    subst bundle
    exact RuntimeFieldBundle.reduced_wellFormed schema
      inheritedBooleanCondition condition group fieldDefinition

mutual
  theorem Tree.runtimeReductionBundles_wellFormed
      (schema : Schema) (variableValues : VariableValues)
      (parentType runtimeType : Name)
      (inheritedBooleanCondition : List BooleanLiteral) (tree : Tree)
      : ∀ bundle,
          bundle
            ∈ tree.runtimeReductionBundles schema variableValues parentType
                runtimeType inheritedBooleanCondition
          -> bundle.WellFormed schema := by
    intro bundle hbundle
    rw [Tree.runtimeReductionBundles] at hbundle
    split at hbundle
    · rcases List.mem_append.mp hbundle with hlocal | hbranches
      · rcases List.mem_flatMap.mp hlocal with ⟨group, hgroup, hbundle⟩
        exact group.runtimeBundles_wellFormed schema parentType
          inheritedBooleanCondition tree.condition bundle hbundle
      · exact runtimeReductionBranchBundles_wellFormed schema variableValues
          parentType runtimeType inheritedBooleanCondition
          tree.branches bundle hbranches
    · simp at hbundle
  termination_by sizeOf tree
  decreasing_by
    exact Tree.branches_sizeOf_lt tree

  theorem runtimeReductionBranchBundles_wellFormed
      (schema : Schema) (variableValues : VariableValues)
      (parentType runtimeType : Name)
      (inheritedBooleanCondition : List BooleanLiteral)
      (branches : List (Branch Tree))
      : ∀ bundle,
          bundle
            ∈ runtimeReductionBranchBundles schema variableValues parentType
                runtimeType inheritedBooleanCondition branches
          -> bundle.WellFormed schema := by
    intro bundle hbundle
    cases branches with
    | nil => simp [runtimeReductionBranchBundles] at hbundle
    | cons branch rest =>
        rw [runtimeReductionBranchBundles] at hbundle
        rcases List.mem_append.mp hbundle with hbody | hrest
        · exact branch.body.runtimeReductionBundles_wellFormed schema
            variableValues (branch.condition.parentType parentType)
            runtimeType inheritedBooleanCondition bundle hbody
        · exact runtimeReductionBranchBundles_wellFormed schema variableValues
            parentType runtimeType inheritedBooleanCondition
            rest bundle hrest
  termination_by sizeOf branches
  decreasing_by
    all_goals
      subst branches
      cases branch
      simp_wf
      omega
end

theorem ReductionUnit.runtimeBundles_wellFormed
    (schema : Schema) (variableValues : VariableValues)
    (executionParentType runtimeType : Name) (ref : ObjectRef)
    (unit : ReductionUnit)
    : ∀ bundle,
        bundle
          ∈ unit.runtimeBundles schema variableValues executionParentType runtimeType ref
        -> bundle.WellFormed schema := by
  intro bundle hbundle
  cases unit with
  | reduce parentType inheritedBooleanCondition selectionSet =>
      exact Tree.runtimeReductionBundles_wellFormed schema variableValues
        parentType runtimeType inheritedBooleanCondition
        (ofSelectionSetInScope schema parentType inheritedBooleanCondition selectionSet)
        bundle hbundle
  | identity selectionSet =>
      rcases List.mem_map.mp hbundle with ⟨field, _hfield, rfl⟩
      exact RuntimeFieldBundle.identity_wellFormed schema field

def ReductionUnit.AllRuntimeApplicable
    (schema : Schema) (variableValues : VariableValues) (runtimeType : Name)
    (units : List ReductionUnit)
    : Prop :=
  ∀ unit, unit ∈ units -> unit.RuntimeApplicable schema variableValues runtimeType

theorem ReductionUnit.collectFlatFields_outputSelectionSet
    (schema : Schema) (variableValues : VariableValues)
    (executionParentType runtimeType : Name) (ref : ObjectRef)
    (units : List ReductionUnit)
    (happlicable
      : ReductionUnit.AllRuntimeApplicable schema variableValues runtimeType units)
    : collectFlatFields schema variableValues executionParentType
        (.object runtimeType ref) (ReductionUnit.outputSelectionSet schema units)
      = RuntimeFieldBundle.reducedEntries
          (runtimeBundlesFor schema variableValues executionParentType runtimeType ref
            units) := by
  revert happlicable
  induction units with
  | nil =>
      intro _happlicable; rfl
  | cons unit rest ih =>
      intro happlicable
      cases unit with
      | identity selectionSet =>
          simp only [ReductionUnit.outputSelectionSet, List.flatMap_cons,
            collectFlatFields_append, ReductionUnit.runtimeBundlesFor,
            RuntimeFieldBundle.reducedEntries, List.map_append]
          rw [ReductionUnit.collectFlatFields_output_eq_reducedFields schema
            variableValues executionParentType runtimeType ref (.identity selectionSet)
            (happlicable _ (by simp))]
          have htail := ih fun candidate hcandidate =>
            happlicable candidate (by simp [hcandidate])
          simpa [RuntimeFieldBundle.reducedEntries, ReductionUnit.outputSelectionSet,
            ReductionUnit.runtimeBundlesFor]
            using congrArg
              (fun tail =>
                RuntimeFieldBundle.reducedEntries
                  ((ReductionUnit.identity selectionSet).runtimeBundles schema
                    variableValues executionParentType runtimeType ref)
                ++ tail)
              htail
      | reduce parentType inheritedBooleanCondition selectionSet =>
          simp only [ReductionUnit.outputSelectionSet, List.flatMap_cons,
            collectFlatFields_append, ReductionUnit.runtimeBundlesFor,
            RuntimeFieldBundle.reducedEntries, List.map_append]
          rw [ReductionUnit.collectFlatFields_output_eq_reducedFields schema
            variableValues executionParentType runtimeType ref
            (.reduce parentType inheritedBooleanCondition selectionSet)
            (happlicable _ (by simp))]
          have htail := ih fun candidate hcandidate =>
            happlicable candidate (by simp [hcandidate])
          simpa [RuntimeFieldBundle.reducedEntries, ReductionUnit.outputSelectionSet,
            ReductionUnit.runtimeBundlesFor]
            using congrArg
              (fun tail =>
                RuntimeFieldBundle.reducedEntries
                  ((ReductionUnit.reduce parentType inheritedBooleanCondition
                      selectionSet).runtimeBundles
                    schema variableValues executionParentType runtimeType ref)
                ++ tail)
              htail

theorem ReductionUnit.allSourceFields_runtimeBundlesFor_perm
    (schema : Schema) (variableValues : VariableValues)
    (executionParentType runtimeType : Name) (ref : ObjectRef)
    (units : List ReductionUnit)
    (happlicable
      : ReductionUnit.AllRuntimeApplicable schema variableValues runtimeType units)
    : (RuntimeFieldBundle.allSourceEntries
        (runtimeBundlesFor schema variableValues executionParentType runtimeType
          ref units)).Perm
        (collectFlatFields schema variableValues executionParentType
          (.object runtimeType ref) (ReductionUnit.inputSelectionSet units)) := by
  revert happlicable
  induction units with
  | nil =>
      intro _happlicable; exact List.Perm.refl []
  | cons unit rest ih =>
      intro happlicable
      rw [ReductionUnit.runtimeBundlesFor, List.flatMap_cons,
        RuntimeFieldBundle.allSourceEntries, List.flatMap_append,
        ReductionUnit.inputSelectionSet, List.flatMap_cons,
        collectFlatFields_append]
      exact List.Perm.append
        (unit.allSourceFields_runtimeBundles_perm schema variableValues
          executionParentType runtimeType ref (happlicable unit (by simp)))
        (ih
          fun candidate hcandidate =>
            happlicable candidate (by simp [hcandidate]))

theorem ReductionUnit.runtimeBundlesFor_wellFormed
    (schema : Schema) (variableValues : VariableValues)
    (executionParentType runtimeType : Name) (ref : ObjectRef)
    (units : List ReductionUnit)
    : ∀ bundle,
        bundle
          ∈ runtimeBundlesFor schema variableValues executionParentType
              runtimeType ref units
        -> bundle.WellFormed schema := by
  intro bundle hbundle
  rcases List.mem_flatMap.mp hbundle with ⟨unit, hunit, hbundle⟩
  exact unit.runtimeBundles_wellFormed schema variableValues executionParentType
    runtimeType ref bundle hbundle

theorem ReductionUnit.reducedGroups_permutationEquivalent
    (schema : Schema) (variableValues : VariableValues)
    (executionParentType runtimeType : Name) (ref : ObjectRef)
    (units : List ReductionUnit) (targetSelectionSet : List Selection)
    (happlicable
      : ReductionUnit.AllRuntimeApplicable schema variableValues runtimeType units)
    (houtput : (ReductionUnit.outputSelectionSet schema units).Perm targetSelectionSet)
    : let bundles :=
        runtimeBundlesFor schema variableValues executionParentType runtimeType ref units
      RuntimeGroupsPermutationEquivalent
        (reducedBundleGroups (groupRuntimeFieldBundles bundles))
        (collectFields schema variableValues executionParentType
          (.object runtimeType ref) targetSelectionSet) := by
  dsimp only
  let bundles := runtimeBundlesFor schema variableValues executionParentType
    runtimeType ref units
  let output := ReductionUnit.outputSelectionSet schema units
  have hflat := ReductionUnit.collectFlatFields_outputSelectionSet schema
    variableValues executionParentType runtimeType ref units happlicable
  have hcollection := RuntimeExtraction.collectFlatFields_perm_flatten_collectFields schema
    variableValues executionParentType (.object runtimeType ref) targetSelectionSet
  have houtputFlat := RuntimeExtraction.collectFlatFields_perm_of_selectionSet_perm schema
    variableValues executionParentType (.object runtimeType ref) houtput
  constructor
  · exact reducedBundleGroups_group_wellFormed bundles
  · exact collectFields_wellFormed schema variableValues executionParentType
      (.object runtimeType ref) targetSelectionSet
  · rw [reducedBundleGroups_groupRuntimeFieldBundles]
    exact (groupExecutableFields_exact
      (RuntimeFieldBundle.reducedEntries bundles)).1
  · exact (executableGroupNamesNodup_iff_map_fst_nodup _).mp
      (NormalForm.collectFields_namesNodup schema variableValues
        executionParentType (.object runtimeType ref) targetSelectionSet)
  · have hentries :
        (ConditionTree.flattenExecutableFieldGroups
          (reducedBundleGroups (groupRuntimeFieldBundles bundles))).Perm
        (ConditionTree.flattenExecutableFieldGroups
          (collectFields schema variableValues executionParentType
            (.object runtimeType ref) targetSelectionSet)) := by
      rw [reducedBundleGroups_groupRuntimeFieldBundles]
      apply (groupExecutableFields_exact
        (RuntimeFieldBundle.reducedEntries bundles)).2.trans
      rw [← hflat]
      exact houtputFlat.trans hcollection
    simpa [ConditionTree.flattenExecutableFieldGroups,
      Execution.FieldGroups.flattenExecutableFieldGroups_eq_flatMap] using hentries

theorem ReductionUnit.sourceGroups_permutationEquivalent
    (schema : Schema) (variableValues : VariableValues)
    (executionParentType runtimeType : Name) (ref : ObjectRef)
    (units : List ReductionUnit) (targetSelectionSet : List Selection)
    (happlicable
      : ReductionUnit.AllRuntimeApplicable schema variableValues runtimeType units)
    (hinput : (ReductionUnit.inputSelectionSet units).Perm targetSelectionSet)
    : let bundles :=
        runtimeBundlesFor schema variableValues executionParentType runtimeType ref units
      RuntimeGroupsPermutationEquivalent
        (sourceBundleGroups (groupRuntimeFieldBundles bundles))
        (collectFields schema variableValues executionParentType
          (.object runtimeType ref) targetSelectionSet) := by
  dsimp only
  let bundles := runtimeBundlesFor schema variableValues executionParentType
    runtimeType ref units
  have hbundles := ReductionUnit.runtimeBundlesFor_wellFormed schema
    variableValues executionParentType runtimeType ref units
  have hsource := ReductionUnit.allSourceFields_runtimeBundlesFor_perm schema
    variableValues executionParentType runtimeType ref units happlicable
  have hinputFlat := RuntimeExtraction.collectFlatFields_perm_of_selectionSet_perm schema
    variableValues executionParentType (.object runtimeType ref) hinput
  have htarget := RuntimeExtraction.collectFlatFields_perm_flatten_collectFields schema
    variableValues
    executionParentType (.object runtimeType ref) targetSelectionSet
  constructor
  · exact sourceBundleGroups_group_wellFormed schema bundles hbundles
  · exact collectFields_wellFormed schema variableValues executionParentType
      (.object runtimeType ref) targetSelectionSet
  · exact sourceBundleGroups_group_keysNodup bundles
  · exact (executableGroupNamesNodup_iff_map_fst_nodup _).mp
      (NormalForm.collectFields_namesNodup schema variableValues
        executionParentType (.object runtimeType ref) targetSelectionSet)
  · simpa [ConditionTree.flattenExecutableFieldGroups,
      Execution.FieldGroups.flattenExecutableFieldGroups_eq_flatMap]
      using (flatten_sourceBundleGroups_group_perm bundles).trans
        (hsource.trans (hinputFlat.trans htarget))

-----------------------------------------------------------------------------------------
-- Applicability of recursively generated child units
-----------------------------------------------------------------------------------------

theorem childInheritedBooleanCondition_allows
    (variableValues : VariableValues)
    (inheritedBooleanCondition conditionBooleanCondition : List BooleanLiteral)
    (hinherited : booleanConditionAllows variableValues inheritedBooleanCondition = true)
    (hcondition : booleanConditionAllows variableValues conditionBooleanCondition = true)
    : booleanConditionAllows variableValues
        ((canonicalBooleanCondition
            (inheritedBooleanCondition ++ conditionBooleanCondition)).getD
          inheritedBooleanCondition)
      = true := by
  have happend : booleanConditionAllows variableValues
      (inheritedBooleanCondition ++ conditionBooleanCondition) = true := by
    rw [booleanConditionAllows_append, hinherited, hcondition]
    rfl
  cases hcanonical
        : canonicalBooleanCondition
            (inheritedBooleanCondition ++ conditionBooleanCondition) with
  | none =>
      have hfalse := canonicalBooleanCondition_none_not_allows variableValues
        (inheritedBooleanCondition ++ conditionBooleanCondition) hcanonical
      rw [happend] at hfalse
      contradiction
  | some childCondition =>
      simp only [Option.getD]
      rw [← canonicalBooleanCondition_some_allows variableValues
        (inheritedBooleanCondition ++ conditionBooleanCondition) childCondition
        hcanonical]
      exact happend

def RuntimeFieldBundle.ChildrenRuntimeApplicable
    (schema : Schema) (variableValues : VariableValues) (childRuntimeType : Name)
    (bundle : RuntimeFieldBundle)
    : Prop :=
  ReductionUnit.AllRuntimeApplicable schema variableValues childRuntimeType
    [bundle.childUnit]

theorem FieldGroup.runtimeBundles_childrenRuntimeApplicable
    (schema : Schema) (variableValues : VariableValues)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (parentType runtimeType : Name)
    (inheritedBooleanCondition : List BooleanLiteral) (condition : Condition)
    (group : FieldGroup)
    (hinherited : booleanConditionAllows variableValues inheritedBooleanCondition = true)
    (hcondition : condition.allows variableValues runtimeType = true)
    (hparentPossible : (schema.getPossibleTypes parentType).contains runtimeType = true)
    : ∀ bundle,
        bundle
          ∈ group.runtimeBundles schema parentType inheritedBooleanCondition condition
        -> ∀ runtimeFieldDefinition,
            schema.lookupField runtimeType bundle.reducedField.fieldName
              = some runtimeFieldDefinition
            -> ∀ childRuntimeType,
                schema.typeIncludesObjectBool
                    runtimeFieldDefinition.outputType.namedType childRuntimeType
                  = true
                -> bundle.ChildrenRuntimeApplicable schema variableValues
                    childRuntimeType := by
  intro bundle hbundle runtimeFieldDefinition hruntimeLookup childRuntimeType
    hchildRuntime
  unfold FieldGroup.runtimeBundles at hbundle
  cases hstaticLookup : schema.lookupField parentType group.first.fieldName with
  | none =>
      simp only [hstaticLookup] at hbundle
      rcases List.mem_map.mp hbundle with ⟨field, _hfield, rfl⟩
      intro unit hunit
      have : unit = .identity
          (Field.toExecutable field).selectionSet := by
        simpa [RuntimeFieldBundle.identity] using List.mem_singleton.mp hunit
      subst unit
      simp [ReductionUnit.RuntimeApplicable]
  | some staticFieldDefinition =>
      simp only [hstaticLookup] at hbundle
      have hbundleEq : bundle = RuntimeFieldBundle.reduced schema
          inheritedBooleanCondition condition group staticFieldDefinition := by
        simpa using List.mem_singleton.mp hbundle
      subst bundle
      intro unit hunit
      have hunitEq : unit = .reduce staticFieldDefinition.outputType.namedType
            ((canonicalBooleanCondition
              (inheritedBooleanCondition ++ condition.booleanCondition)).getD
              inheritedBooleanCondition)
            group.mergedSelectionSet := by
        simpa [RuntimeFieldBundle.reduced] using List.mem_singleton.mp hunit
      subst unit
      simp only [ReductionUnit.RuntimeApplicable]
      constructor
      · apply childInheritedBooleanCondition_allows variableValues
          inheritedBooleanCondition condition.booleanCondition hinherited
        have hallows := hcondition
        simp only [Condition.allows, Bool.and_eq_true] at hallows
        exact hallows.2
      · have hsubtype :=
          SchemaWellFormedness.schemaWellFormed_possibleObject_lookupField_outputTypeSubtype
            hschema (List.contains_iff_mem.mp hparentPossible) hstaticLookup
              (by simpa [RuntimeFieldBundle.reduced] using hruntimeLookup)
        exact typeIncludesObjectBool_of_outputTypeSubtype_namedType schema hsubtype
          hchildRuntime

mutual
  theorem Tree.runtimeReductionBundles_childrenRuntimeApplicable
      (schema : Schema) (variableValues : VariableValues)
      (hschema : SchemaWellFormedness.schemaWellFormed schema)
      (parentType runtimeType : Name)
      (inheritedBooleanCondition : List BooleanLiteral) (tree : Tree)
      (hinherited
        : booleanConditionAllows variableValues inheritedBooleanCondition = true)
      (hparentPossible : (schema.getPossibleTypes parentType).contains runtimeType = true)
      (hcoherent : tree.BranchesCoherent schema inheritedBooleanCondition)
      : ∀ bundle,
          bundle
            ∈ tree.runtimeReductionBundles schema variableValues parentType
                runtimeType inheritedBooleanCondition
          -> ∀ runtimeFieldDefinition,
              schema.lookupField runtimeType bundle.reducedField.fieldName
                = some runtimeFieldDefinition
              -> ∀ childRuntimeType,
                  schema.typeIncludesObjectBool
                      runtimeFieldDefinition.outputType.namedType childRuntimeType
                    = true
                  -> bundle.ChildrenRuntimeApplicable schema variableValues
                      childRuntimeType := by
    intro bundle hbundle runtimeFieldDefinition hruntimeLookup childRuntimeType
      hchildRuntime
    rw [Tree.runtimeReductionBundles] at hbundle
    split at hbundle
    · rename_i hcondition
      rcases List.mem_append.mp hbundle with hlocal | hbranches
      · rcases List.mem_flatMap.mp hlocal with ⟨group, hgroup, hbundle⟩
        exact group.runtimeBundles_childrenRuntimeApplicable schema variableValues
          hschema parentType runtimeType inheritedBooleanCondition tree.condition
          hinherited hcondition hparentPossible bundle hbundle runtimeFieldDefinition
          hruntimeLookup childRuntimeType hchildRuntime
      · exact runtimeReductionBranchBundles_childrenRuntimeApplicable schema
          variableValues hschema parentType runtimeType inheritedBooleanCondition
          tree.condition tree.branches hinherited hcondition hparentPossible
          (by simpa [Tree.BranchesCoherent] using hcoherent) bundle hbranches
          runtimeFieldDefinition hruntimeLookup childRuntimeType hchildRuntime
    · simp at hbundle
  termination_by sizeOf tree
  decreasing_by
    exact Tree.branches_sizeOf_lt tree

  theorem runtimeReductionBranchBundles_childrenRuntimeApplicable
      (schema : Schema) (variableValues : VariableValues)
      (hschema : SchemaWellFormedness.schemaWellFormed schema)
      (parentType runtimeType : Name)
      (inheritedBooleanCondition : List BooleanLiteral)
      (parentCondition : Condition) (branches : List (Branch Tree))
      (hinherited
        : booleanConditionAllows variableValues inheritedBooleanCondition = true)
      (hparentCondition : parentCondition.allows variableValues runtimeType = true)
      (hparentPossible : (schema.getPossibleTypes parentType).contains runtimeType = true)
      (hcoherent
        : branchesCoherent schema inheritedBooleanCondition parentCondition branches)
      : ∀ bundle,
          bundle
            ∈ runtimeReductionBranchBundles schema variableValues parentType
                runtimeType inheritedBooleanCondition branches
          -> ∀ runtimeFieldDefinition,
              schema.lookupField runtimeType bundle.reducedField.fieldName
                = some runtimeFieldDefinition
              -> ∀ childRuntimeType,
                  schema.typeIncludesObjectBool
                      runtimeFieldDefinition.outputType.namedType childRuntimeType
                    = true
                  -> bundle.ChildrenRuntimeApplicable schema variableValues
                      childRuntimeType := by
    intro bundle hbundle runtimeFieldDefinition hruntimeLookup childRuntimeType
      hchildRuntime
    cases branches with
    | nil => simp [runtimeReductionBranchBundles] at hbundle
    | cons branch rest =>
        rw [branchesCoherent] at hcoherent
        rw [runtimeReductionBranchBundles] at hbundle
        rcases List.mem_append.mp hbundle with hbody | hrest
        · have hbodyCondition :
              branch.body.condition.allows variableValues runtimeType = true := by
            rw [Tree.runtimeReductionBundles] at hbody
            split at hbody
            · assumption
            · simp at hbody
          have hnext := conditionForBranch?_runtime schema variableValues runtimeType
            inheritedBooleanCondition parentCondition branch.condition hinherited
          rw [hcoherent.1] at hnext
          simp only [conditionOptionAllows] at hnext
          have hbranchAllows :
              branch.condition.allows schema variableValues runtimeType = true := by
            cases hallows : branch.condition.allows schema variableValues runtimeType
            · have hfalse :
                  branch.body.condition.allows variableValues runtimeType = false := by
                simpa [hparentCondition, hallows] using hnext
              rw [hbodyCondition] at hfalse
              contradiction
            · rfl
          have hbranchParentPossible
              : (schema.getPossibleTypes
                  (branch.condition.parentType parentType)).contains
                  runtimeType
                = true := by
            cases hbranchCondition : branch.condition with
            | typeCondition typeName =>
                change (schema.getPossibleTypes typeName).contains runtimeType = true
                rw [hbranchCondition] at hbranchAllows
                simpa only [BranchCondition.allows,
                  Schema.typeIncludesObjectBool] using hbranchAllows
            | booleanLiteral literal =>
                change (schema.getPossibleTypes parentType).contains runtimeType = true
                exact hparentPossible
          exact branch.body.runtimeReductionBundles_childrenRuntimeApplicable schema
            variableValues hschema (branch.condition.parentType parentType) runtimeType
            inheritedBooleanCondition hinherited hbranchParentPossible hcoherent.2.1
            bundle hbody runtimeFieldDefinition hruntimeLookup childRuntimeType
            hchildRuntime
        · exact runtimeReductionBranchBundles_childrenRuntimeApplicable schema
            variableValues hschema parentType runtimeType inheritedBooleanCondition
            parentCondition rest hinherited hparentCondition hparentPossible
            hcoherent.2.2 bundle hrest runtimeFieldDefinition hruntimeLookup
            childRuntimeType hchildRuntime
  termination_by sizeOf branches
  decreasing_by
    all_goals
      subst branches
      cases branch
      simp_wf
      omega
end

theorem ReductionUnit.runtimeBundles_childrenRuntimeApplicable
    (schema : Schema) (variableValues : VariableValues)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (runtimeType : Name) (ref : ObjectRef) (unit : ReductionUnit)
    (happlicable : unit.RuntimeApplicable schema variableValues runtimeType)
    : ∀ bundle,
        bundle ∈ unit.runtimeBundles schema variableValues runtimeType runtimeType ref
        -> ∀ runtimeFieldDefinition,
            schema.lookupField runtimeType bundle.reducedField.fieldName
              = some runtimeFieldDefinition
            -> ∀ childRuntimeType,
                schema.typeIncludesObjectBool
                    runtimeFieldDefinition.outputType.namedType childRuntimeType
                  = true
                -> bundle.ChildrenRuntimeApplicable schema variableValues
                    childRuntimeType := by
  intro bundle hbundle runtimeFieldDefinition hruntimeLookup childRuntimeType
    hchildRuntime
  cases unit with
  | reduce parentType inheritedBooleanCondition selectionSet =>
      simp only [ReductionUnit.RuntimeApplicable] at happlicable
      exact Tree.runtimeReductionBundles_childrenRuntimeApplicable schema
        variableValues hschema parentType runtimeType inheritedBooleanCondition
        (ofSelectionSetInScope schema parentType inheritedBooleanCondition selectionSet)
        happlicable.1 happlicable.2
        (ofSelectionSetInScope_branchesCoherent schema parentType
          inheritedBooleanCondition selectionSet)
        bundle hbundle runtimeFieldDefinition hruntimeLookup childRuntimeType
        hchildRuntime
  | identity selectionSet =>
      rcases List.mem_map.mp hbundle with ⟨field, _hfield, rfl⟩
      intro childUnit hchildUnit
      have : childUnit = .identity field.2.selectionSet := by
        simpa [RuntimeFieldBundle.identity] using List.mem_singleton.mp hchildUnit
      subst childUnit
      simp [ReductionUnit.RuntimeApplicable]

theorem ReductionUnit.runtimeBundlesFor_childrenRuntimeApplicable
    (schema : Schema) (variableValues : VariableValues)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (runtimeType : Name) (ref : ObjectRef) (units : List ReductionUnit)
    (happlicable
      : ReductionUnit.AllRuntimeApplicable schema variableValues runtimeType units)
    : ∀ bundle,
        bundle ∈ runtimeBundlesFor schema variableValues runtimeType runtimeType ref units
        -> ∀ runtimeFieldDefinition,
            schema.lookupField runtimeType bundle.reducedField.fieldName
              = some runtimeFieldDefinition
            -> ∀ childRuntimeType,
                schema.typeIncludesObjectBool
                    runtimeFieldDefinition.outputType.namedType childRuntimeType
                  = true
                -> bundle.ChildrenRuntimeApplicable schema variableValues
                    childRuntimeType := by
  intro bundle hbundle runtimeFieldDefinition hruntimeLookup childRuntimeType
    hchildRuntime
  rcases List.mem_flatMap.mp hbundle with ⟨unit, hunit, hbundle⟩
  exact unit.runtimeBundles_childrenRuntimeApplicable schema variableValues hschema
    runtimeType ref (happlicable unit hunit) bundle hbundle runtimeFieldDefinition
    hruntimeLookup childRuntimeType hchildRuntime

def RuntimeFieldBundle.GroupsChildrenRuntimeApplicable
    (schema : Schema) (variableValues : VariableValues) (runtimeType : Name)
    (groups : List (Name × List RuntimeFieldBundle))
    : Prop :=
  ∀ bundle,
    bundle ∈ flattenRuntimeFieldBundleGroups groups
    -> ∀ runtimeFieldDefinition,
        schema.lookupField runtimeType bundle.reducedField.fieldName
          = some runtimeFieldDefinition
        -> ∀ childRuntimeType,
            schema.typeIncludesObjectBool
                runtimeFieldDefinition.outputType.namedType childRuntimeType
              = true
            -> bundle.ChildrenRuntimeApplicable schema variableValues childRuntimeType

end ConditionTree
end GraphQL
