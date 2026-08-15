import Proofs.GraphQL.Theories.TreeSummary.Syntactic.RuntimeGroups
import Proofs.GraphQL.Theories.ConditionTree.KnownFalsePruning

/-! Runtime field coverage and runtime-type selection for Syntactic summaries. -/

namespace GraphQL
namespace TreeSummary
namespace Syntactic

open GraphQL.Execution
open GraphQL.ConditionTree
open GraphQL.ConditionTree.Termination
open GraphQL.Algorithms.ExecutionUngroupedUncached.Eager
open TreeSummary.Measure

universe u v

-----------------------------------------------------------------------------------------
-- Runtime coverage by stored condition-tree groups
-----------------------------------------------------------------------------------------

def allCollectedGroups (parentType : Name)
    (inheritedBooleanCondition : List BooleanLiteral) (tree : Tree)
    : List CollectedFieldGroup :=
  traversedCollectedGroups parentType inheritedBooleanCondition tree .all

-- Occurrence-preserving reverse coverage. Besides witnessing that an active static
-- group is concrete, it remembers which concrete field came from each stored field
-- selection; recursive execution uses that fact when merged child selections are
-- collected.
def groupsRepresentFields {ObjectRef : Type}
    (schema : Schema) (variableValues : VariableValues)
    (executionParentType runtimeType : Name)
    (source : ResolverValue ObjectRef)
    (availableGroups : List CollectedFieldGroup)
    (fields : List ExecutableField)
    : Prop :=
  ∀ group,
    group ∈ availableGroups
    -> group.selections ≠ []
        ∧ ∀ selection,
            selection ∈ group.selections
            -> group.condition.allows variableValues runtimeType = true
            -> ∃ field,
                field ∈ fields
                ∧ groupCoversField schema variableValues executionParentType runtimeType
                    source group field
                ∧ selection
                  = .field group.responseName field.fieldName field.arguments []
                      field.selectionSet

theorem fieldName_mem_of_groupsRepresentField
    {ObjectRef : Type}
    (schema : Schema) (variableValues : VariableValues)
    (runtimeType : Name) (ref : ObjectRef)
    (groups : List CollectedFieldGroup) (field : ExecutableField)
    (hmatch : groupsRepresentField schema variableValues runtimeType ref groups field)
    (group : CollectedFieldGroup) (hgroup : group ∈ groups)
    : field.fieldName ∈ group.fieldNames := by
  rcases hmatch group hgroup with
    ⟨candidate, _hcover, hcandidateName, _harguments,
      selection, hselection, hselectionEq⟩
  rw [← hcandidateName]
  simp [CollectedFieldGroup.selections,
    ConditionTree.FieldGroup.selections, ConditionTree.Field.toSelection,
    hselectionEq] at hselection
  rcases hselection with ⟨field, hfield, _hresponseName, hfieldName, _⟩
  exact List.mem_map.mpr ⟨field, hfield, hfieldName⟩

-- Validation facts retained for one concrete response-name group. They are generic
-- execution invariants; analyses only consume field identity compatibility.
def ExecutableFieldsChildrenValid (schema : Schema) (fields : List ExecutableField)
    : Prop :=
  ∀ first definition childRuntime,
    first ∈ fields
    -> schema.lookupField first.parentType first.fieldName = some definition
    -> schema.typeIncludesObjectBool definition.outputType.namedType childRuntime = true
    -> schema.objectType childRuntime
        ∧ NormalForm.selectionSetSemanticsReady schema childRuntime
            (Execution.mergedFieldSelectionSet fields)
        ∧ FieldMerge.fieldsInSetCanMerge schema childRuntime
            (Execution.mergedFieldSelectionSet fields)

def ExecutableGroupsValid (schema : Schema) (groups : List (Name × List ExecutableField))
    : Prop :=
  ∀ responseName fields,
    (responseName, fields) ∈ groups
    -> ExecutableFieldsFieldValidationMergeCompatible fields
        ∧ ExecutableFieldsChildrenValid schema fields
        ∧ ExecutableFieldsArgumentsNodup fields
        ∧ ∀ field, field ∈ fields -> selectionSetArgumentsNodup field.selectionSet

theorem groupsRepresentField_of_represent_and_compatible
    {ObjectRef : Type}
    (schema : Schema) (variableValues : VariableValues)
    (runtimeType : Name) (ref : ObjectRef)
    (groups : List CollectedFieldGroup) (fields : List ExecutableField)
    (field : ExecutableField)
    (hfield : field ∈ fields)
    (hnames : ExecutableFieldsResponseName field.responseName fields)
    (hcompatible : ExecutableFieldsFieldValidationMergeCompatible fields)
    (hconditions
      : ∀ group,
          group ∈ groups -> group.condition.allows variableValues runtimeType = true)
    (hrepresent
      : groupsRepresentFields schema variableValues runtimeType runtimeType
          (.object runtimeType ref) groups fields)
    : groupsRepresentField schema variableValues runtimeType ref groups field := by
  intro group hgroup
  rcases hrepresent group hgroup with ⟨hfields, hselections⟩
  let selection := group.selections.head hfields
  rcases hselections selection (List.head_mem hfields) (hconditions group hgroup) with
    ⟨candidate, hcandidate, hcover, hselection⟩
  have hresponse : candidate.responseName = field.responseName := by
    exact hnames candidate hcandidate
  rcases hcompatible candidate field hcandidate hfield hresponse with
    ⟨hfieldName, harguments⟩
  exact ⟨candidate, hcover, hfieldName, harguments, selection,
    List.head_mem hfields, hselection⟩

theorem groupsCoverFields_activeGroupsWithResponseName
    {ObjectRef : Type}
    (schema : Schema) (variableValues : VariableValues)
    (executionParentType runtimeType responseName : Name)
    (ref : ObjectRef) (groups : List CollectedFieldGroup)
    (fields : List ExecutableField)
    (hnames : ∀ field, field ∈ fields -> field.responseName = responseName)
    (hcover
      : groupsCoverFields schema variableValues executionParentType runtimeType
          (.object runtimeType ref) groups fields)
    : groupsCoverFields schema variableValues executionParentType runtimeType
        (.object runtimeType ref)
        (activeGroupsWithResponseName variableValues runtimeType responseName groups)
        fields := by
  intro field hfield
  rcases hcover field hfield with ⟨group, hgroup, hgroupCover⟩
  refine ⟨group, ?_, hgroupCover⟩
  apply List.mem_filter.mpr
  refine ⟨hgroup, ?_⟩
  have hname : group.responseName = responseName :=
    hgroupCover.2.2.1.symm.trans (hnames field hfield)
  simp [hname, hgroupCover.1]

theorem activeGroupsWithResponseName_ne_nil_of_cover
    {ObjectRef : Type}
    (schema : Schema) (variableValues : VariableValues)
    (executionParentType runtimeType responseName : Name)
    (ref : ObjectRef) (groups : List CollectedFieldGroup)
    (field : ExecutableField) (rest : List ExecutableField)
    (hnames
      : ∀ candidate, candidate ∈ field :: rest -> candidate.responseName = responseName)
    (hcover
      : groupsCoverFields schema variableValues executionParentType runtimeType
          (.object runtimeType ref) groups (field :: rest))
    : activeGroupsWithResponseName variableValues runtimeType responseName groups
      ≠ [] := by
  intro hnil
  have hactive := groupsCoverFields_activeGroupsWithResponseName schema variableValues
    executionParentType runtimeType responseName ref groups (field :: rest) hnames
    hcover
  rcases hactive field (by simp) with ⟨group, hgroup, _hgroupCover⟩
  simp [hnil] at hgroup

theorem collectFlatFields_mem_of_selection_mem
    {ObjectRef : Type}
    (schema : Schema) (variableValues : VariableValues)
    (executionParentType : Name) (source : ResolverValue ObjectRef)
    (selections : List Selection) (selection : Selection)
    (field : ExecutableField)
    (hselection : selection ∈ selections)
    (hfield
      : field
        ∈ collectFlatFields schema variableValues executionParentType source [selection])
    : field
      ∈ collectFlatFields schema variableValues executionParentType source
          selections := by
  induction selections with
  | nil => contradiction
  | cons head rest ih =>
      rw [collectFlatFields]
      simp only [List.mem_append]
      cases hselection with
      | head => exact Or.inl (by simpa [collectFlatFields] using hfield)
      | tail _ htail => exact Or.inr (ih htail)

theorem traversedCollectedGroup_selection_producesField
    {ObjectRef : Type}
    (schema : Schema) (variableValues pruningValues : VariableValues)
    (hmatch : BooleanValuesMatchForPruning variableValues pruningValues)
    (parentType : Name) (inheritedBooleanCondition : List BooleanLiteral)
    (selectionSet : List Selection) (executionParentType runtimeType : Name)
    (ref : ObjectRef) (traversal : Traversal) (group : CollectedFieldGroup)
    (hinherited : booleanConditionAllows variableValues inheritedBooleanCondition = true)
    (hpossible : (schema.getPossibleTypes parentType).contains runtimeType = true)
    (hgroup
      : group
        ∈ traversedCollectedGroups parentType inheritedBooleanCondition
            (ofSelectionSetInScopeWithKnownFalsePruning schema parentType
              inheritedBooleanCondition pruningValues selectionSet)
            traversal)
    (hcondition : group.condition.allows variableValues runtimeType = true)
    (selection : Selection) (hselection : selection ∈ group.selections)
    : ∃ field,
        field
          ∈ flattenCollectedFields
              (collectFields schema variableValues executionParentType
                (.object runtimeType ref) selectionSet)
        ∧ groupCoversField schema variableValues executionParentType runtimeType
            (.object runtimeType ref) group field
        ∧ selection
          = .field group.responseName field.fieldName field.arguments []
              field.selectionSet := by
  let tree :=
    ofSelectionSetInScopeWithKnownFalsePruning schema parentType inheritedBooleanCondition
      pruningValues selectionSet
  have hshape := traversedCollectedGroup_shape parentType inheritedBooleanCondition tree
    traversal group (by simpa [tree] using hgroup)
  rcases hshape.2 selection hselection with ⟨storedField, hselectionEq, hentry⟩
  cases storedField with
  | mk fieldName arguments children =>
      have hselection' :
          .field group.responseName fieldName arguments [] children
            ∈ group.selections := by
        have hselectionTo :
            Field.toSelection group.responseName
                { fieldName, arguments, selectionSet := children }
              ∈ group.selections := by
          rw [← hselectionEq]
          exact hselection
        simpa [Field.toSelection] using hselectionTo
      have hentry' :
          (group.condition,
            .field group.responseName fieldName arguments [] children)
            ∈ tree.fieldEntries := by
        have hentryTo :
            (group.condition,
              Field.toSelection group.responseName
                { fieldName, arguments, selectionSet := children })
              ∈ tree.fieldEntries := by
          rw [← hselectionEq]
          exact hentry
        simpa [Field.toSelection] using hentryTo
      let field : ExecutableField :=
        {
          parentType := executionParentType
          responseName := group.responseName
          fieldName
          arguments
          selectionSet := children
        }
      have htreeField :
          field ∈ tree.collectRuntimeFields variableValues executionParentType
            runtimeType := by
        rw [Tree.collectRuntimeFields,
          runtimeFieldsForEntries_eq_projected schema variableValues executionParentType
            runtimeType (.object runtimeType ref),
          ← tree.fieldEntries_eq_map_storedFieldEntries]
        unfold runtimeFieldsForConditionEntries
        apply List.mem_flatMap.mpr
        refine ⟨(group.condition,
          .field group.responseName fieldName arguments [] children), hentry', ?_⟩
        simp [hcondition, field]
      have hcollected :=
        (ConditionTree.knownFalsePruning_sound schema parentType
          inheritedBooleanCondition variableValues pruningValues selectionSet hmatch
          executionParentType runtimeType ref hinherited hpossible field).mp
          (by simpa [tree] using htreeField)
      refine ⟨field, hcollected, ⟨hcondition, ?_, rfl, ?_⟩, ?_⟩
      · apply collectFlatFields_mem_of_selection_mem schema variableValues
          executionParentType (.object runtimeType ref) group.selections
          (.field group.responseName fieldName arguments [] children) field
          hselection'
        simp [collectFlatFields, collectFlatSelection, selectionDirectivesAllowBool,
          field]
      · intro candidate hcandidate
        rcases hshape.2 candidate hcandidate with ⟨candidateField, heq, _hentry⟩
        rw [heq]
        simp [Field.toSelection, Selection.responseName?]
      · simpa [field, Field.toSelection] using hselectionEq

theorem traversedCollectedGroup_producesField
    {ObjectRef : Type}
    (schema : Schema) (variableValues : VariableValues)
    (parentType : Name) (inheritedBooleanCondition : List BooleanLiteral)
    (selectionSet : List Selection) (executionParentType runtimeType : Name)
    (ref : ObjectRef) (traversal : Traversal) (group : CollectedFieldGroup)
    (hinherited : booleanConditionAllows variableValues inheritedBooleanCondition = true)
    (hpossible : (schema.getPossibleTypes parentType).contains runtimeType = true)
    (hgroup
      : group
        ∈ traversedCollectedGroups parentType inheritedBooleanCondition
            (ofSelectionSetInScopeWithKnownFalsePruning schema parentType
              inheritedBooleanCondition [] selectionSet)
            traversal)
    (hcondition : group.condition.allows variableValues runtimeType = true)
    : ∃ field,
        field
          ∈ flattenCollectedFields
              (collectFields schema variableValues executionParentType
                (.object runtimeType ref) selectionSet)
        ∧ groupCoversField schema variableValues executionParentType runtimeType
            (.object runtimeType ref) group field := by
  have hshape := traversedCollectedGroup_shape parentType inheritedBooleanCondition
    (ofSelectionSetInScopeWithKnownFalsePruning schema parentType inheritedBooleanCondition []
      selectionSet)
    traversal group hgroup
  let selection := group.selections.head hshape.1
  have hmatch : BooleanValuesMatchForPruning variableValues [] := by
    intro variableName value hvalue
    simp [inputValueBoolean?, lookupVariableValue?] at hvalue
  rcases traversedCollectedGroup_selection_producesField schema variableValues [] hmatch
      parentType inheritedBooleanCondition selectionSet executionParentType runtimeType
      ref traversal group hinherited hpossible hgroup hcondition selection
      (List.head_mem hshape.1) with
    ⟨field, hfield, hcover, _hselection⟩
  exact ⟨field, hfield, hcover⟩

mutual
  theorem fieldEntry_mem_allCollectedGroups
      (parentType : Name)
      (inheritedBooleanCondition : List BooleanLiteral)
      (tree : Tree) (entry : Condition × Selection)
      (hentry : entry ∈ tree.fieldEntries)
      : ∃ group,
          group ∈ allCollectedGroups parentType inheritedBooleanCondition tree
          ∧ group.condition = entry.1
          ∧ entry.2 ∈ group.selections
          ∧ entry.2.responseName? = some group.responseName
          ∧ ∀ selection,
              selection ∈ group.selections
              -> selection.responseName? = some group.responseName := by
    simp only [Tree.fieldEntries, List.mem_append] at hentry
    cases hentry with
    | inl hlocal =>
        have hlocal' :=
          (mem_annotatedFieldGroups tree.condition entry.1 entry.2 tree.fields).mp
            hlocal
        obtain ⟨fieldGroup, hfieldGroup, hselection⟩ :=
          List.mem_flatMap.mp hlocal'.2
        let group : CollectedFieldGroup :=
          {
            inheritedBooleanCondition
            condition := tree.condition
            fieldGroup
          }
        refine ⟨group, ?_, hlocal'.1.symm, hselection, ?_, ?_⟩
        · unfold allCollectedGroups traversedCollectedGroups
          apply List.mem_append_left
          exact List.mem_map.mpr ⟨fieldGroup, hfieldGroup, rfl⟩
        · rcases List.mem_map.mp hselection with ⟨field, _hfield, heq⟩
          rw [← heq]
          simp [group, CollectedFieldGroup.responseName, Field.toSelection,
            Selection.responseName?]
        · intro selection hselection
          rcases List.mem_map.mp hselection with ⟨field, _hfield, heq⟩
          rw [← heq]
          simp [group, CollectedFieldGroup.responseName, Field.toSelection,
            Selection.responseName?]
    | inr hbranches =>
        rcases branchFieldEntry_mem_allCollectedGroups parentType
            inheritedBooleanCondition tree.branches entry hbranches with
          ⟨group, hgroup, hcondition, hselection, hresponseName, hkeyed⟩
        exact ⟨
          group,
          by
            simp [allCollectedGroups, traversedCollectedGroups, hgroup],
          hcondition,
          hselection,
          hresponseName,
          hkeyed
        ⟩
  termination_by sizeOf tree
  decreasing_by
    cases tree
    simp_all
    omega

  theorem branchFieldEntry_mem_allCollectedGroups
      (parentType : Name)
      (inheritedBooleanCondition : List BooleanLiteral)
      (branches : List (Branch Tree)) (entry : Condition × Selection)
      (hentry : entry ∈ branchFieldEntries branches)
      : ∃ group,
          group
            ∈ traversedBranchCollectedGroups parentType
                inheritedBooleanCondition branches .all
          ∧ group.condition = entry.1
          ∧ entry.2 ∈ group.selections
          ∧ entry.2.responseName? = some group.responseName
          ∧ ∀ selection,
              selection ∈ group.selections
              -> selection.responseName? = some group.responseName := by
    cases branches with
    | nil => simp [branchFieldEntries] at hentry
    | cons branch rest =>
        simp only [branchFieldEntries, List.mem_append] at hentry
        cases hentry with
        | inl hbody =>
            rcases fieldEntry_mem_allCollectedGroups
                (branch.condition.parentType parentType)
                inheritedBooleanCondition branch.body entry hbody with
              ⟨group, hgroup, hcondition, hselection, hresponseName, hkeyed⟩
            exact ⟨
              group,
              by
                have hinclude : Traversal.all.includeBranch branch.condition = true :=
                  rfl
                simp only [traversedBranchCollectedGroups, hinclude, if_true,
                  List.mem_append]
                exact Or.inl hgroup,
              hcondition,
              hselection,
              hresponseName,
              hkeyed
            ⟩
        | inr hrest =>
            rcases branchFieldEntry_mem_allCollectedGroups parentType
                inheritedBooleanCondition rest entry hrest with
              ⟨group, hgroup, hcondition, hselection, hresponseName, hkeyed⟩
            exact ⟨
              group,
              by
                simpa [traversedBranchCollectedGroups] using Or.inr hgroup,
              hcondition,
              hselection,
              hresponseName,
              hkeyed
            ⟩
  termination_by sizeOf branches
  decreasing_by
    all_goals
      try subst branches
      cases branch
      simp_wf
      omega
end

theorem collectFlatFields_responseName_eq
    {ObjectRef : Type}
    (schema : Schema) (variableValues : VariableValues)
    (executionParentType : Name) (source : ResolverValue ObjectRef)
    (selection : Selection) (field : ExecutableField) (responseName : Name)
    (hselection : selection.responseName? = some responseName)
    (hfield
      : field
        ∈ collectFlatFields schema variableValues executionParentType source [selection])
    : field.responseName = responseName := by
  cases selection with
  | field selectionResponseName fieldName arguments directives selectionSet =>
      simp only [Selection.responseName?, Option.some.injEq] at hselection
      subst selectionResponseName
      cases hdirectives : selectionDirectivesAllowBool variableValues directives <;>
        simp [collectFlatFields, collectFlatSelection, hdirectives] at hfield
      subst field
      rfl
  | inlineFragment typeCondition directives selectionSet =>
      simp [Selection.responseName?] at hselection

theorem executableField_responseName_mem_of_flatten_mem
    (groups : List (Name × List ExecutableField))
    (hwellFormed : NormalForm.executableGroupsWellFormed groups)
    (field : ExecutableField) (hfield : field ∈ flattenCollectedFields groups)
    : field.responseName ∈ groups.map Prod.fst := by
  rcases (mem_flattenCollectedFields_iff groups field).mp hfield with
    ⟨responseName, fields, hgroup, hmember⟩
  have hresponse := (hwellFormed (responseName, fields) hgroup).2 field hmember
  simpa [hresponse] using List.mem_map_of_mem (f := Prod.fst) hgroup

theorem groupsWithoutResponseName_cover_tail
    {ObjectRef : Type}
    (schema : Schema) (variableValues : VariableValues)
    (runtimeType responseName : Name) (ref : ObjectRef)
    (fields : List ExecutableField)
    (rest : List (Name × List ExecutableField))
    (groups : List CollectedFieldGroup)
    (hwellFormed : NormalForm.executableGroupsWellFormed ((responseName, fields) :: rest))
    (hnodup : NormalForm.executableGroupNamesNodup ((responseName, fields) :: rest))
    (hcover
      : groupsCoverFields schema variableValues runtimeType runtimeType
          (.object runtimeType ref) groups
          (flattenCollectedFields ((responseName, fields) :: rest)))
    : groupsCoverFields schema variableValues runtimeType runtimeType
        (.object runtimeType ref) (groupsWithoutResponseName responseName groups)
        (flattenCollectedFields rest) := by
  intro field hfield
  have hfieldAll :
      field ∈ flattenCollectedFields ((responseName, fields) :: rest) := by
    rw [flattenCollectedFields]
    exact List.mem_append.mpr (Or.inr hfield)
  rcases hcover field hfieldAll with ⟨group, hgroup, hgroupCover⟩
  refine ⟨group, ?_, hgroupCover⟩
  apply List.mem_filter.mpr
  refine ⟨hgroup, ?_⟩
  have hrestWellFormed :=
    NormalForm.GroundTypeNormalization.executableGroupsWellFormed_tail hwellFormed
  have hfieldName :=
    executableField_responseName_mem_of_flatten_mem rest hrestWellFormed field hfield
  have hne : group.responseName ≠ responseName := by
    intro hequal
    apply hnodup.1
    rw [← hequal, ← hgroupCover.2.2.1]
    exact hfieldName
  simp [hne]

theorem runtimeField_mem_allCollectedGroups
    {ObjectRef : Type}
    (schema : Schema) (variableValues : VariableValues)
    (executionParentType runtimeType : Name)
    (source : ResolverValue ObjectRef)
    (parentType : Name)
    (inheritedBooleanCondition : List BooleanLiteral)
    (tree : Tree) (field : ExecutableField)
    (hfield
      : field ∈ tree.collectRuntimeFields variableValues executionParentType runtimeType)
    : ∃ group,
        group ∈ allCollectedGroups parentType inheritedBooleanCondition tree
        ∧ groupCoversField schema variableValues executionParentType runtimeType source
            group field := by
  simp only [Tree.collectRuntimeFields, runtimeFieldsForEntries,
    List.mem_flatMap] at hfield
  rcases hfield with ⟨entry, hentry, hfield⟩
  cases hcondition : entry.1.allows variableValues runtimeType with
  | false => simp [hcondition] at hfield
  | true =>
      simp only [hcondition, if_true] at hfield
      have hrawEntry : projectStoredFieldEntry entry ∈ tree.fieldEntries := by
        rw [tree.fieldEntries_eq_map_storedFieldEntries]
        exact List.mem_map.mpr ⟨entry, hentry, rfl⟩
      rcases fieldEntry_mem_allCollectedGroups parentType inheritedBooleanCondition tree
          (projectStoredFieldEntry entry) hrawEntry with
        ⟨group, hgroup, hgcondition, hgselection, hgresponseName, hgkeyed⟩
      refine ⟨group, hgroup, ?_, ?_, ?_, ?_⟩
      · rw [hgcondition]
        exact hcondition
      · apply collectFlatFields_mem_of_selection_mem schema variableValues
          executionParentType source group.selections (projectStoredFieldEntry entry).2
          field hgselection
        simpa [projectStoredFieldEntry, NamedField.toSelection, Field.toSelection,
          collectFlatFields, collectFlatSelection, selectionDirectivesAllowBool] using
          hfield
      · exact collectFlatFields_responseName_eq schema variableValues
          executionParentType source (projectStoredFieldEntry entry).2 field
          group.responseName hgresponseName
          (by
            simpa [projectStoredFieldEntry, NamedField.toSelection, Field.toSelection,
              collectFlatFields, collectFlatSelection,
              selectionDirectivesAllowBool] using hfield)
      · exact hgkeyed

theorem extractedGroups_cover_collectedFields
    {ObjectRef : Type}
    (schema : Schema) (variableValues : VariableValues)
    (executionParentType runtimeType : Name) (ref : ObjectRef)
    (parentType : Name)
    (inheritedBooleanCondition : List BooleanLiteral)
    (selectionSet : List Selection)
    (hinherited : booleanConditionAllows variableValues inheritedBooleanCondition = true)
    (hpossible : (schema.getPossibleTypes parentType).contains runtimeType = true)
    : groupsCoverFields schema variableValues executionParentType runtimeType
        (.object runtimeType ref)
        (allCollectedGroups parentType inheritedBooleanCondition
          (ofSelectionSetInScope schema parentType inheritedBooleanCondition
            selectionSet))
        (flattenCollectedFields
          (collectFields schema variableValues executionParentType
            (.object runtimeType ref) selectionSet)) := by
  intro field hfield
  have hruntime :=
    (ConditionTree.extraction_sound schema parentType inheritedBooleanCondition
      selectionSet (ObjectRef := ObjectRef) variableValues executionParentType
      runtimeType ref hinherited hpossible field).mpr hfield
  exact runtimeField_mem_allCollectedGroups schema variableValues executionParentType
    runtimeType (.object runtimeType ref) parentType inheritedBooleanCondition
    (ofSelectionSetInScope schema parentType inheritedBooleanCondition selectionSet)
    field hruntime

theorem Traversal.withVariableValues_includeBranch_of_allows
    (schema : Schema) (variableValues : VariableValues) (runtimeType : Name)
    (branch : BranchCondition)
    (hallows : branch.allows schema variableValues runtimeType = true)
    : (Traversal.withVariableValues variableValues).includeBranch branch = true := by
  cases branch with
  | typeCondition typeName => rfl
  | booleanLiteral literal =>
      cases literal with
      | positive variableName =>
          cases hvalue : inputValueBoolean? variableValues (.variable variableName) with
          | none =>
              simp [BranchCondition.allows, BooleanLiteral.allows,
                BooleanLiteral.toDirective, directiveAllowsSelectionBool, hvalue]
                at hallows
          | some value =>
              cases value <;>
                simp [Traversal.withVariableValues, evaluateBooleanLiteral?,
                  BranchCondition.allows, BooleanLiteral.allows,
                  BooleanLiteral.variableName, BooleanLiteral.requiredValue,
                  BooleanLiteral.toDirective, directiveAllowsSelectionBool, hvalue]
                  at hallows ⊢
      | negative variableName =>
          cases hvalue : inputValueBoolean? variableValues (.variable variableName) with
          | none =>
              simp [Traversal.withVariableValues, evaluateBooleanLiteral?, hvalue,
                BooleanLiteral.variableName, BooleanLiteral.requiredValue]
          | some value =>
              cases value <;>
                simp [Traversal.withVariableValues, evaluateBooleanLiteral?,
                  BranchCondition.allows, BooleanLiteral.allows,
                  BooleanLiteral.variableName, BooleanLiteral.requiredValue,
                  BooleanLiteral.toDirective, directiveAllowsSelectionBool, hvalue]
                  at hallows ⊢

mutual
  theorem fieldEntry_mem_traversedCollectedGroups
      (schema : Schema) (variableValues : VariableValues) (runtimeType : Name)
      (traversal : Traversal)
      (htraversal
        : ∀ branch,
            branch.allows schema variableValues runtimeType = true
            -> traversal.includeBranch branch = true)
      (parentType : Name)
      (inheritedBooleanCondition : List BooleanLiteral)
      (tree : Tree) (entry : Condition × Selection)
      (hcoherent : tree.BranchesCoherent schema inheritedBooleanCondition)
      (hinherited
        : booleanConditionAllows variableValues inheritedBooleanCondition = true)
      (hentry : entry ∈ tree.fieldEntries)
      (hallows : entry.1.allows variableValues runtimeType = true)
      : tree.condition.allows variableValues runtimeType = true
        ∧ ∃ group,
            group
              ∈ traversedCollectedGroups parentType inheritedBooleanCondition tree
                  traversal
            ∧ group.condition = entry.1
            ∧ entry.2 ∈ group.selections
            ∧ entry.2.responseName? = some group.responseName
            ∧ ∀ selection,
                selection ∈ group.selections
                -> selection.responseName? = some group.responseName := by
    simp only [Tree.fieldEntries, List.mem_append] at hentry
    cases hentry with
    | inl hlocal =>
        have hlocal' :=
          (mem_annotatedFieldGroups tree.condition entry.1 entry.2 tree.fields).mp
            hlocal
        obtain ⟨fieldGroup, hfieldGroup, hselection⟩ :=
          List.mem_flatMap.mp hlocal'.2
        let group : CollectedFieldGroup :=
          {
            inheritedBooleanCondition
            condition := tree.condition
            fieldGroup
          }
        refine ⟨?_, group, ?_, hlocal'.1.symm, hselection, ?_, ?_⟩
        · simpa [hlocal'.1] using hallows
        · unfold traversedCollectedGroups
          apply List.mem_append_left
          exact List.mem_map.mpr ⟨fieldGroup, hfieldGroup, rfl⟩
        · rcases List.mem_map.mp hselection with ⟨field, _hfield, heq⟩
          rw [← heq]
          simp [group, CollectedFieldGroup.responseName, Field.toSelection,
            Selection.responseName?]
        · intro selection hselection
          rcases List.mem_map.mp hselection with ⟨field, _hfield, heq⟩
          rw [← heq]
          simp [group, CollectedFieldGroup.responseName, Field.toSelection,
            Selection.responseName?]
    | inr hbranches =>
        rw [Tree.BranchesCoherent] at hcoherent
        rcases branchFieldEntry_mem_traversedCollectedGroups schema variableValues
            runtimeType traversal htraversal parentType inheritedBooleanCondition
            tree.condition tree.branches entry hcoherent hinherited hbranches hallows with
          ⟨htree, group, hgroup, hcondition, hselection, hresponseName, hkeyed⟩
        exact ⟨
          htree,
          group,
          by
            simp only [traversedCollectedGroups, List.mem_append]
            exact Or.inr hgroup,
          hcondition,
          hselection,
          hresponseName,
          hkeyed
        ⟩
  termination_by sizeOf tree
  decreasing_by
    cases tree
    simp_all
    omega

  theorem branchFieldEntry_mem_traversedCollectedGroups
      (schema : Schema) (variableValues : VariableValues) (runtimeType : Name)
      (traversal : Traversal)
      (htraversal
        : ∀ branch,
            branch.allows schema variableValues runtimeType = true
            -> traversal.includeBranch branch = true)
      (parentType : Name)
      (inheritedBooleanCondition : List BooleanLiteral)
      (parentCondition : Condition)
      (branches : List (Branch Tree)) (entry : Condition × Selection)
      (hcoherent
        : branchesCoherent schema inheritedBooleanCondition parentCondition branches)
      (hinherited
        : booleanConditionAllows variableValues inheritedBooleanCondition = true)
      (hentry : entry ∈ branchFieldEntries branches)
      (hallows : entry.1.allows variableValues runtimeType = true)
      : parentCondition.allows variableValues runtimeType = true
        ∧ ∃ group,
            group
              ∈ traversedBranchCollectedGroups parentType
                  inheritedBooleanCondition branches traversal
            ∧ group.condition = entry.1
            ∧ entry.2 ∈ group.selections
            ∧ entry.2.responseName? = some group.responseName
            ∧ ∀ selection,
                selection ∈ group.selections
                -> selection.responseName? = some group.responseName := by
    cases branches with
    | nil => simp [branchFieldEntries] at hentry
    | cons branch rest =>
        rw [branchesCoherent] at hcoherent
        simp only [branchFieldEntries, List.mem_append] at hentry
        cases hentry with
        | inl hbody =>
            rcases fieldEntry_mem_traversedCollectedGroups schema variableValues
                runtimeType traversal htraversal (branch.condition.parentType parentType)
                inheritedBooleanCondition branch.body entry hcoherent.2.1 hinherited hbody
                hallows with
              ⟨hbodyAllows, group, hgroup, hcondition, hselection, hresponseName,
                hkeyed⟩
            have hnext := conditionForBranch?_runtime schema variableValues runtimeType
              inheritedBooleanCondition parentCondition branch.condition
              hinherited
            rw [hcoherent.1] at hnext
            simp only [conditionOptionAllows] at hnext
            rw [hbodyAllows] at hnext
            have hboth := Bool.and_eq_true_iff.mp hnext.symm
            have hinclude := htraversal branch.condition hboth.2
            exact ⟨
              hboth.1,
              group,
              by
                simp only [traversedBranchCollectedGroups, hinclude, if_true,
                  List.mem_append]
                exact Or.inl hgroup,
              hcondition,
              hselection,
              hresponseName,
              hkeyed
            ⟩
        | inr hrest =>
            rcases branchFieldEntry_mem_traversedCollectedGroups schema variableValues
                runtimeType traversal htraversal parentType inheritedBooleanCondition
                parentCondition rest entry hcoherent.2.2 hinherited hrest hallows with
              ⟨hparent, group, hgroup, hcondition, hselection, hresponseName, hkeyed⟩
            exact ⟨
              hparent,
              group,
              by
                simpa [traversedBranchCollectedGroups] using Or.inr hgroup,
              hcondition,
              hselection,
              hresponseName,
              hkeyed
            ⟩
  termination_by sizeOf branches
  decreasing_by
    all_goals
      try subst branches
      cases branch
      simp_wf
      omega
end

theorem runtimeField_mem_traversedCollectedGroups
    {ObjectRef : Type}
    (schema : Schema) (variableValues : VariableValues)
    (executionParentType runtimeType : Name)
    (source : ResolverValue ObjectRef)
    (traversal : Traversal)
    (htraversal
      : ∀ branch,
          branch.allows schema variableValues runtimeType = true
          -> traversal.includeBranch branch = true)
    (parentType : Name)
    (inheritedBooleanCondition : List BooleanLiteral)
    (tree : Tree) (field : ExecutableField)
    (hinherited : booleanConditionAllows variableValues inheritedBooleanCondition = true)
    (hcoherent : tree.BranchesCoherent schema inheritedBooleanCondition)
    (hfield
      : field ∈ tree.collectRuntimeFields variableValues executionParentType runtimeType)
    : ∃ group,
        group
          ∈ traversedCollectedGroups parentType inheritedBooleanCondition tree traversal
        ∧ groupCoversField schema variableValues executionParentType runtimeType source
            group field := by
  simp only [Tree.collectRuntimeFields, runtimeFieldsForEntries,
    List.mem_flatMap] at hfield
  rcases hfield with ⟨entry, hentry, hfield⟩
  cases hcondition : entry.1.allows variableValues runtimeType with
  | false => simp [hcondition] at hfield
  | true =>
      simp only [hcondition, if_true] at hfield
      have hrawEntry : projectStoredFieldEntry entry ∈ tree.fieldEntries := by
        rw [tree.fieldEntries_eq_map_storedFieldEntries]
        exact List.mem_map.mpr ⟨entry, hentry, rfl⟩
      rcases fieldEntry_mem_traversedCollectedGroups schema variableValues runtimeType
          traversal htraversal parentType inheritedBooleanCondition tree
          (projectStoredFieldEntry entry) hcoherent hinherited hrawEntry hcondition with
        ⟨_treeAllows, group, hgroup, hgcondition, hgselection, hgresponseName,
          hgkeyed⟩
      refine ⟨group, hgroup, ?_, ?_, ?_, ?_⟩
      · rw [hgcondition]
        exact hcondition
      · apply collectFlatFields_mem_of_selection_mem schema variableValues
          executionParentType source group.selections (projectStoredFieldEntry entry).2
          field hgselection
        simpa [projectStoredFieldEntry, NamedField.toSelection, Field.toSelection,
          collectFlatFields, collectFlatSelection, selectionDirectivesAllowBool] using
          hfield
      · exact collectFlatFields_responseName_eq schema variableValues
          executionParentType source (projectStoredFieldEntry entry).2 field
          group.responseName hgresponseName
          (by
            simpa [projectStoredFieldEntry, NamedField.toSelection, Field.toSelection,
              collectFlatFields, collectFlatSelection,
              selectionDirectivesAllowBool] using hfield)
      · exact hgkeyed

-- A traversal is execution-complete when every runtime-collected field remains covered
-- by one of the statically traversed groups at every selection-set boundary.
def Traversal.ExecutionComplete (traversal : Traversal)
    (schema : Schema) (variableValues : VariableValues)
    : Prop :=
  ∀ {ObjectRef : Type}
    (parentType : Name) (inheritedBooleanCondition : List BooleanLiteral)
    (selectionSet : List Selection)
    (executionParentType runtimeType : Name) (ref : ObjectRef),
    booleanConditionAllows variableValues inheritedBooleanCondition = true
    -> (schema.getPossibleTypes parentType).contains runtimeType = true
    -> groupsCoverFields schema variableValues executionParentType runtimeType
        (.object runtimeType ref)
        (traversedCollectedGroups parentType inheritedBooleanCondition
          (ofSelectionSetInScopeWithKnownFalsePruning schema parentType
            inheritedBooleanCondition traversal.summaryVariableValues selectionSet)
          (traversal.atRuntimeType schema runtimeType))
        (flattenCollectedFields
          (collectFields schema variableValues executionParentType
            (.object runtimeType ref) selectionSet))

theorem Traversal.all_executionComplete (schema : Schema)
    (variableValues : VariableValues)
    : Traversal.all.ExecutionComplete schema variableValues := by
  intro ObjectRef parentType inheritedBooleanCondition selectionSet
    executionParentType runtimeType ref hinherited hpossible field hfield
  have hmatch : BooleanValuesMatchForPruning variableValues [] := by
    intro variableName value hvalue
    simp [inputValueBoolean?, lookupVariableValue?] at hvalue
  have hruntime :=
    (ConditionTree.knownFalsePruning_sound schema parentType
      inheritedBooleanCondition variableValues [] selectionSet hmatch
      (ObjectRef := ObjectRef) executionParentType runtimeType ref hinherited hpossible
      field).mpr hfield
  exact runtimeField_mem_traversedCollectedGroups schema variableValues
    executionParentType runtimeType (.object runtimeType ref)
    (Traversal.all.atRuntimeType schema runtimeType)
    (by
      intro branch hallows
      cases branch with
      | typeCondition typeName =>
          simpa [Traversal.atRuntimeType, Traversal.includeBranchAtRuntimeType,
            BranchCondition.allows] using hallows
      | booleanLiteral literal =>
          simp [Traversal.atRuntimeType, Traversal.includeBranchAtRuntimeType,
            Traversal.all])
    parentType inheritedBooleanCondition
    (ofSelectionSetInScopeWithKnownFalsePruning schema parentType inheritedBooleanCondition []
      selectionSet)
    field hinherited
    (ofSelectionSetInScopeWithKnownFalsePruning_branchesCoherent schema parentType
      inheritedBooleanCondition [] selectionSet)
    hruntime

theorem Traversal.withVariableValues_executionComplete
    (schema : Schema) (variableValues : VariableValues)
    : (Traversal.withVariableValues variableValues).ExecutionComplete schema
        variableValues := by
  intro ObjectRef parentType inheritedBooleanCondition selectionSet
    executionParentType runtimeType ref hinherited hpossible field hfield
  have hmatch : BooleanValuesMatchForPruning variableValues variableValues := by
    intro variableName value hvalue
    simp [hvalue]
  have hruntime :=
    (ConditionTree.knownFalsePruning_sound schema parentType
      inheritedBooleanCondition variableValues variableValues selectionSet hmatch
      (ObjectRef := ObjectRef) executionParentType runtimeType ref hinherited hpossible
      field).mpr hfield
  exact runtimeField_mem_traversedCollectedGroups schema variableValues
    executionParentType runtimeType (.object runtimeType ref)
    ((Traversal.withVariableValues variableValues).atRuntimeType schema runtimeType)
    (by
      intro branch hallows
      cases branch with
      | typeCondition typeName =>
          simpa [Traversal.atRuntimeType, Traversal.includeBranchAtRuntimeType,
            BranchCondition.allows] using hallows
      | booleanLiteral literal =>
          exact Traversal.withVariableValues_includeBranch_of_allows schema
            variableValues runtimeType (.booleanLiteral literal) hallows)
    parentType
    inheritedBooleanCondition
    (ofSelectionSetInScopeWithKnownFalsePruning schema parentType inheritedBooleanCondition
      variableValues selectionSet)
    field hinherited
    (ofSelectionSetInScopeWithKnownFalsePruning_branchesCoherent schema parentType
      inheritedBooleanCondition variableValues selectionSet)
    hruntime

theorem Traversal.withRuntimeBooleanDefaults_executionComplete
    (schema : Schema) (variableValues : VariableValues)
    (summaryVariableValues : VariableValues := [])
    (hmatch : BooleanValuesMatchForPruning variableValues summaryVariableValues)
    : (Traversal.withRuntimeBooleanDefaults variableValues
        summaryVariableValues).ExecutionComplete
        schema variableValues := by
  intro ObjectRef parentType inheritedBooleanCondition selectionSet
    executionParentType runtimeType ref hinherited hpossible field hfield
  have hruntime :=
    (ConditionTree.knownFalsePruning_sound schema parentType
      inheritedBooleanCondition variableValues summaryVariableValues selectionSet hmatch
      (ObjectRef := ObjectRef) executionParentType runtimeType ref hinherited hpossible
      field).mpr hfield
  exact runtimeField_mem_traversedCollectedGroups schema variableValues
    executionParentType runtimeType (.object runtimeType ref)
    ((Traversal.withRuntimeBooleanDefaults variableValues summaryVariableValues
      ).atRuntimeType schema runtimeType)
    (by
      intro branch hallows
      cases branch with
      | typeCondition typeName =>
          simpa [Traversal.atRuntimeType, Traversal.includeBranchAtRuntimeType,
            BranchCondition.allows] using hallows
      | booleanLiteral literal =>
          cases literal with
          | positive variableName =>
              have hvalue :
                  inputValueBoolean? variableValues (.variable variableName)
                    = some true := by
                cases hraw :
                    inputValueBoolean? variableValues (.variable variableName) with
                | none =>
                    simp [BranchCondition.allows, BooleanLiteral.allows,
                      BooleanLiteral.toDirective, directiveAllowsSelectionBool, hraw]
                      at hallows
                | some value =>
                    cases value <;>
                      simp [BranchCondition.allows, BooleanLiteral.allows,
                        BooleanLiteral.toDirective, directiveAllowsSelectionBool, hraw]
                        at hallows
                    rfl
              simp [Traversal.atRuntimeType, Traversal.includeBranchAtRuntimeType,
                Traversal.withRuntimeBooleanDefaults, runtimeBooleanDefault, hvalue,
                BooleanLiteral.variableName, BooleanLiteral.requiredValue]
          | negative variableName =>
              cases hraw :
                  inputValueBoolean? variableValues (.variable variableName) with
              | none =>
                  simp [Traversal.atRuntimeType, Traversal.includeBranchAtRuntimeType,
                    Traversal.withRuntimeBooleanDefaults, runtimeBooleanDefault, hraw,
                    BooleanLiteral.variableName, BooleanLiteral.requiredValue]
              | some value =>
                  have hvalue : value = false := by
                    cases value with
                    | false => rfl
                    | true =>
                        simp [BranchCondition.allows, BooleanLiteral.allows,
                          BooleanLiteral.toDirective, directiveAllowsSelectionBool,
                          hraw] at hallows
                  simp [Traversal.atRuntimeType, Traversal.includeBranchAtRuntimeType,
                    Traversal.withRuntimeBooleanDefaults, runtimeBooleanDefault, hraw,
                    hvalue, BooleanLiteral.variableName, BooleanLiteral.requiredValue])
    parentType inheritedBooleanCondition
    (ofSelectionSetInScopeWithKnownFalsePruning schema parentType inheritedBooleanCondition
      summaryVariableValues selectionSet)
    field hinherited
    (ofSelectionSetInScopeWithKnownFalsePruning_branchesCoherent schema parentType
      inheritedBooleanCondition summaryVariableValues selectionSet)
    hruntime

theorem activeGroupsWithResponseName_conditionAllows
    (variableValues : VariableValues) (runtimeType responseName : Name)
    (groups : List CollectedFieldGroup)
    : conditionsAllowGroupsAt variableValues runtimeType
        (activeGroupsWithResponseName variableValues runtimeType responseName
          groups) := by
  intro group hgroup
  exact (Bool.and_eq_true_iff.mp (List.mem_filter.mp hgroup).2).2

theorem inheritedConditionsAllowGroups_filter
    (variableValues : VariableValues) (groups : List CollectedFieldGroup)
    (keep : CollectedFieldGroup -> Bool)
    (hallows : inheritedConditionsAllowGroups variableValues groups)
    : inheritedConditionsAllowGroups variableValues (groups.filter keep) := by
  intro group hgroup
  exact hallows group (List.mem_filter.mp hgroup).1

theorem childInheritedBooleanCondition_allows
    (variableValues : VariableValues) (group : CollectedFieldGroup)
    (hinherited
      : booleanConditionAllows variableValues group.inheritedBooleanCondition = true)
    (hcondition : group.condition.allows variableValues runtimeType = true)
    : booleanConditionAllows variableValues group.childInheritedBooleanCondition
      = true := by
  have hnode :
      booleanConditionAllows variableValues group.condition.booleanCondition = true :=
    (Bool.and_eq_true_iff.mp hcondition).2
  have hsource :
      booleanConditionAllows variableValues
          (group.inheritedBooleanCondition ++ group.condition.booleanCondition) = true := by
    rw [booleanConditionAllows_append, hinherited, hnode]
    rfl
  cases hcanonical
        : canonicalBooleanCondition
            (group.inheritedBooleanCondition ++ group.condition.booleanCondition) with
  | none =>
      have hfalse :=
        canonicalBooleanCondition_none_not_allows variableValues
          (group.inheritedBooleanCondition ++ group.condition.booleanCondition)
          hcanonical
      rw [hsource] at hfalse
      contradiction
  | some canonical =>
      unfold CollectedFieldGroup.childInheritedBooleanCondition
      rw [hcanonical]
      simp only [Option.getD_some]
      rw [← canonicalBooleanCondition_some_allows variableValues
        (group.inheritedBooleanCondition ++ group.condition.booleanCondition)
        canonical hcanonical]
      exact hsource

mutual
  theorem traversedCollectedGroups_inherited
      (parentType : Name) (inheritedBooleanCondition : List BooleanLiteral)
      (tree : Tree) (traversal : Traversal)
      : ∀ group,
          group
            ∈ traversedCollectedGroups parentType inheritedBooleanCondition tree traversal
          -> group.inheritedBooleanCondition = inheritedBooleanCondition := by
    intro group hgroup
    simp only [traversedCollectedGroups, List.mem_append] at hgroup
    cases hgroup with
    | inl hlocal =>
        rcases List.mem_map.mp hlocal with ⟨fieldGroup, _hfieldGroup, rfl⟩
        rfl
    | inr hbranches =>
        exact traversedBranchCollectedGroups_inherited parentType
          inheritedBooleanCondition tree.branches traversal group hbranches
  termination_by sizeOf tree
  decreasing_by
    cases tree
    simp_all
    omega

  theorem traversedBranchCollectedGroups_inherited
      (parentType : Name) (inheritedBooleanCondition : List BooleanLiteral)
      (branches : List (Branch Tree)) (traversal : Traversal)
      : ∀ group,
          group
            ∈ traversedBranchCollectedGroups parentType inheritedBooleanCondition
                branches traversal
          -> group.inheritedBooleanCondition = inheritedBooleanCondition := by
    cases branches with
    | nil => simp [traversedBranchCollectedGroups]
    | cons branch rest =>
        intro group hgroup
        simp only [traversedBranchCollectedGroups, List.mem_append] at hgroup
        cases hgroup with
        | inl hbody =>
            cases hinclude : traversal.includeBranch branch.condition with
            | false => simp [hinclude] at hbody
            | true =>
                exact traversedCollectedGroups_inherited
                  (branch.condition.parentType parentType)
                  inheritedBooleanCondition branch.body traversal group
                  (by simpa [hinclude] using hbody)
        | inr hrest =>
            exact traversedBranchCollectedGroups_inherited parentType
              inheritedBooleanCondition rest traversal group hrest
  termination_by sizeOf branches
  decreasing_by
    all_goals
      cases branch
      simp_wf
      omega
end

theorem candidateChildGroupsFor_inheritedConditionAllows
    (schema : Schema) (variableValues : VariableValues)
    (parentRuntimeType childParentType childRuntimeType : Name)
    (groups : List CollectedFieldGroup) (traversal : Traversal)
    (hallows : inheritedConditionsAllowGroups variableValues groups)
    (hconditions : conditionsAllowGroupsAt variableValues parentRuntimeType groups)
    : inheritedConditionsAllowGroups variableValues
        (candidateChildGroupsFor schema childParentType childRuntimeType traversal
          groups) := by
  intro childGroup hchildGroup
  simp only [candidateChildGroupsFor, List.mem_flatMap] at hchildGroup
  rcases hchildGroup with ⟨group, hgroup, hchildGroup⟩
  have hchildInherited := childInheritedBooleanCondition_allows variableValues group
    (hallows group hgroup) (hconditions group hgroup)
  have heq := traversedCollectedGroups_inherited childParentType
    group.childInheritedBooleanCondition
    (group.childTreeWithKnownFalsePruning schema childParentType traversal.summaryVariableValues)
    (traversal.atRuntimeType schema childRuntimeType) childGroup hchildGroup
  rw [heq]
  exact hchildInherited

theorem collectFlatFields_mem_source
    {ObjectRef : Type}
    (schema : Schema) (variableValues : VariableValues)
    (executionParentType : Name) (source : ResolverValue ObjectRef)
    (selections : List Selection) (field : ExecutableField)
    (hfield
      : field
        ∈ collectFlatFields schema variableValues executionParentType source selections)
    : ∃ selection,
        selection ∈ selections
        ∧ field
          ∈ collectFlatFields schema variableValues executionParentType source
              [selection] := by
  induction selections with
  | nil => simp [collectFlatFields] at hfield
  | cons selection rest ih =>
      rw [collectFlatFields] at hfield
      simp only [List.mem_append] at hfield
      cases hfield with
      | inl hhead => exact ⟨selection, by simp, by simpa [collectFlatFields] using hhead⟩
      | inr hrest =>
          rcases ih hrest with ⟨candidate, hcandidate, hcandidateField⟩
          exact ⟨candidate, by simp [hcandidate], hcandidateField⟩

theorem mergeSelectionSets_eq_flatMap (selections : List Selection)
    : SelectionSet.mergeSelectionSets selections
      = selections.flatMap Selection.subselections :=
  rfl

theorem mergeSelectionSets_mem_of_selection_mem
    (selections : List Selection) (selection child : Selection)
    (hselection : selection ∈ selections)
    (hchild : child ∈ selection.subselections)
    : child ∈ SelectionSet.mergeSelectionSets selections := by
  rw [mergeSelectionSets_eq_flatMap]
  simp only [List.mem_flatMap]
  exact ⟨selection, hselection, hchild⟩

theorem mergeSelectionSets_mem_source
    (selections : List Selection) (child : Selection)
    (hchild : child ∈ SelectionSet.mergeSelectionSets selections)
    : ∃ selection, selection ∈ selections ∧ child ∈ selection.subselections := by
  rw [mergeSelectionSets_eq_flatMap] at hchild
  simpa only [List.mem_flatMap] using hchild

theorem groupCoversField_child_mem_mergedSelectionSet
    {ObjectRef : Type}
    (schema : Schema) (variableValues : VariableValues)
    (executionParentType parentRuntimeType : Name)
    (parentSource : ResolverValue ObjectRef)
    (childRuntimeType : Name) (childSource : ResolverValue ObjectRef)
    (group : CollectedFieldGroup) (field child : ExecutableField)
    (hcover
      : groupCoversField schema variableValues executionParentType parentRuntimeType
          parentSource group field)
    (hchild
      : child
        ∈ collectFlatFields schema variableValues childRuntimeType childSource
            field.selectionSet)
    : child
      ∈ collectFlatFields schema variableValues childRuntimeType childSource
          group.mergedSelectionSet := by
  rcases hcover with ⟨_hcondition, hfield, _hresponseName, hkeyed⟩
  rcases collectFlatFields_mem_source schema variableValues executionParentType
      parentSource group.selections field hfield with
    ⟨selection, hselection, hfieldSelection⟩
  have hresponse := hkeyed selection hselection
  cases selection with
  | field responseName fieldName arguments directives selectionSet =>
      cases hdirectives : selectionDirectivesAllowBool variableValues directives <;>
        simp [collectFlatFields, collectFlatSelection, hdirectives] at hfieldSelection
      subst field
      rcases collectFlatFields_mem_source schema variableValues childRuntimeType
          childSource selectionSet child hchild with
        ⟨childSelection, hchildSelection, hchildSingleton⟩
      apply collectFlatFields_mem_of_selection_mem schema variableValues
        childRuntimeType childSource group.mergedSelectionSet childSelection child
      · exact mergeSelectionSets_mem_of_selection_mem group.selections
          (.field responseName fieldName arguments directives selectionSet)
          childSelection hselection hchildSelection
      · exact hchildSingleton
  | inlineFragment typeCondition directives selectionSet =>
      simp [Selection.responseName?] at hresponse

theorem collectFlatFields_append
    {ObjectRef : Type}
    (schema : Schema) (variableValues : VariableValues)
    (parentType : Name) (source : ResolverValue ObjectRef)
    (left right : List Selection)
    : collectFlatFields schema variableValues parentType source (left ++ right)
      = collectFlatFields schema variableValues parentType source left
        ++ collectFlatFields schema variableValues parentType source right := by
  induction left with
  | nil => simp [collectFlatFields]
  | cons selection rest ih => simp [collectFlatFields, ih, List.append_assoc]

theorem collectFlatFields_mergedFieldSelectionSet_mem
    {ObjectRef : Type}
    (schema : Schema) (variableValues : VariableValues)
    (parentType : Name) (source : ResolverValue ObjectRef)
    (fields : List ExecutableField) (child : ExecutableField)
    (hchild
      : child
        ∈ collectFlatFields schema variableValues parentType source
            (Execution.mergedFieldSelectionSet fields))
    : ∃ field,
        field ∈ fields
        ∧ child
          ∈ collectFlatFields schema variableValues parentType source
              field.selectionSet := by
  induction fields with
  | nil => simp [Execution.mergedFieldSelectionSet, collectFlatFields] at hchild
  | cons field rest ih =>
      rw [Execution.mergedFieldSelectionSet_cons, collectFlatFields_append] at hchild
      rcases List.mem_append.mp hchild with hhead | htail
      · exact ⟨field, by simp, hhead⟩
      · rcases ih htail with ⟨candidate, hcandidate, hcandidateChild⟩
        exact ⟨candidate, by simp [hcandidate], hcandidateChild⟩

theorem objectType_getPossibleTypes_contains_self
    (schema : Schema) (runtimeType : Name)
    (hobject : schema.objectType runtimeType)
    : (schema.getPossibleTypes runtimeType).contains runtimeType = true := by
  rcases hobject with ⟨objectType, hlookup⟩
  have hname : objectType.name = runtimeType := by
    have hmatch := List.find?_some hlookup
    simpa [Schema.lookupType, TypeDefinition.name] using hmatch
  simp [Schema.getPossibleTypes, hlookup, hname]

theorem collectFields_executableGroupsValid
    {ObjectRef : Type}
    (schema : Schema) (variableValues : VariableValues)
    (runtimeType : Name) (ref : ObjectRef) (selectionSet : List Selection)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (hobject : schema.objectType runtimeType)
    (hready : NormalForm.selectionSetSemanticsReady schema runtimeType selectionSet)
    (hmerge : FieldMerge.fieldsInSetCanMerge schema runtimeType selectionSet)
    (harguments : selectionSetArgumentsNodup selectionSet)
    : ExecutableGroupsValid schema
        (collectFields schema variableValues runtimeType (.object runtimeType ref)
          selectionSet) := by
  let source : ResolverValue ObjectRef := .object runtimeType ref
  let groups := collectFields schema variableValues runtimeType source selectionSet
  have hself : ScopedParentRuntimeApplies schema runtimeType runtimeType := by
    exact NormalForm.object_typeIncludesObjectBool_self schema hobject
  have hlookupValid :
      NormalForm.selectionSetLookupValid schema runtimeType selectionSet :=
    NormalForm.selectionSetLookupValid_of_selectionSetSemanticsReady selectionSet hready
  intro responseName fields hgroup
  have hcompatible : ExecutableFieldsFieldValidationMergeCompatible fields := by
    have hall := collectFields_fieldCompatible_of_canMerge_lookupValid_object schema
      variableValues runtimeType runtimeType runtimeType ref selectionSet hmerge hself
      hlookupValid
    exact hall responseName fields (by simpa [groups, source] using hgroup)
  have hargumentFacts := collectFields_argumentsAndChildrenNodup schema variableValues
    runtimeType source selectionSet harguments
  refine ⟨hcompatible, ?_, ?_, ?_⟩
  · intro first definition childRuntime hfirst hlookup hinclude
    have hchildScoped :
        ScopedParentRuntimeApplies schema childRuntime definition.outputType.namedType :=
      ScopedParentRuntimeApplies.of_typeIncludesObjectBool schema childRuntime
        definition.outputType.namedType hinclude
    have hchildObject : schema.objectType childRuntime :=
      ScopedParentRuntimeApplies.runtimeObjectType schema hschema hchildScoped
    refine ⟨hchildObject, ?_, ?_⟩
    · exact Algorithms.ExecutionUngrouped.collectedGroup_mergedFieldSelectionSet_semanticsReady
        schema variableValues runtimeType runtimeType ref selectionSet responseName fields
        first definition childRuntime hobject hself hready hmerge
        (by simpa [groups, source] using hgroup) hfirst hlookup hinclude
    · exact Algorithms.ExecutionUngrouped.collectedGroup_mergedFieldSelectionSet_canMerge
        schema variableValues runtimeType runtimeType ref selectionSet responseName fields
        hmerge hself hlookupValid (by simpa [groups, source] using hgroup) childRuntime
  · exact hargumentFacts.1 responseName fields (by simpa [groups, source] using hgroup)
  · intro field hfield
    exact hargumentFacts.2 field
      (collectedExecutableFields_mem_of_group_mem
        (by simpa [groups, source] using hgroup) hfield)

theorem candidateChildGroupsFor_cover_subfields
    {ObjectRef : Type}
    (schema : Schema) (variableValues : VariableValues)
    (executionParentType parentRuntimeType : Name) (parentRef : ObjectRef)
    (childParentType childRuntimeType responseName : Name) (childRef : ObjectRef)
    (groups : List CollectedFieldGroup) (fields : List ExecutableField)
    (traversal : Traversal)
    (htraversal : traversal.ExecutionComplete schema variableValues)
    (hpossible
      : (schema.getPossibleTypes childParentType).contains childRuntimeType = true)
    (hallows : inheritedConditionsAllowGroups variableValues groups)
    (_hfields : ∀ field, field ∈ fields -> field.responseName = responseName)
    (hcover
      : groupsCoverFields schema variableValues executionParentType parentRuntimeType
          (.object parentRuntimeType parentRef) groups fields)
    : groupsCoverFields schema variableValues childRuntimeType childRuntimeType
        (.object childRuntimeType childRef)
        (candidateChildGroupsFor schema childParentType childRuntimeType traversal groups)
        (flattenCollectedFields
          (collectSubfields schema variableValues childRuntimeType
            (.object childRuntimeType childRef) fields)) := by
  intro child hchild
  have hchildCollected :
      child
        ∈ flattenCollectedFields
            (collectFields schema variableValues childRuntimeType
              (.object childRuntimeType childRef)
              (Execution.mergedFieldSelectionSet fields)) := by
    simpa [NormalForm.collectSubfields_eq_collectFields_mergedFieldSelectionSet] using
      hchild
  have hchildFlat :
      child
        ∈ collectFlatFields schema variableValues childRuntimeType
            (.object childRuntimeType childRef)
            (Execution.mergedFieldSelectionSet fields) :=
    (collectFlatFields_mem_collectFields schema variableValues childRuntimeType
      (.object childRuntimeType childRef)
      (Execution.mergedFieldSelectionSet fields) child).mpr hchildCollected
  rcases collectFlatFields_mergedFieldSelectionSet_mem schema variableValues
      childRuntimeType (.object childRuntimeType childRef) fields child hchildFlat with
    ⟨field, hfield, hfieldChild⟩
  rcases hcover field hfield with ⟨group, hgroup, hgroupCover⟩
  have hmergedChild :=
    groupCoversField_child_mem_mergedSelectionSet schema variableValues
      executionParentType parentRuntimeType (.object parentRuntimeType parentRef)
      childRuntimeType (.object childRuntimeType childRef)
      group field child hgroupCover hfieldChild
  have hchildGroups :=
    htraversal childParentType group.childInheritedBooleanCondition
      group.mergedSelectionSet childRuntimeType childRuntimeType childRef
      (childInheritedBooleanCondition_allows variableValues group
        (hallows group hgroup) hgroupCover.1)
      hpossible
      child
      ((collectFlatFields_mem_collectFields schema variableValues childRuntimeType
          (.object childRuntimeType childRef) group.mergedSelectionSet child).mp
        hmergedChild)
  rcases hchildGroups with ⟨childGroup, hchildGroup, hchildCover⟩
  refine ⟨childGroup, ?_, hchildCover⟩
  unfold candidateChildGroupsFor candidateChildGroups
  exact List.mem_flatMap.mpr ⟨group, hgroup, hchildGroup⟩

theorem candidateChildGroupsFor_represent_subfields
    {ObjectRef : Type}
    (schema : Schema) (variableValues : VariableValues)
    (parentRuntimeType : Name) (parentRef : ObjectRef)
    (childParentType childRuntimeType : Name) (childRef : ObjectRef)
    (groups : List CollectedFieldGroup) (fields : List ExecutableField)
    (traversal : Traversal)
    (hmatch : BooleanValuesMatchForPruning variableValues traversal.summaryVariableValues)
    (hpossible
      : (schema.getPossibleTypes childParentType).contains childRuntimeType = true)
    (hallows : inheritedConditionsAllowGroups variableValues groups)
    (hconditions : conditionsAllowGroupsAt variableValues parentRuntimeType groups)
    (hrepresent
      : groupsRepresentFields schema variableValues parentRuntimeType parentRuntimeType
          (.object parentRuntimeType parentRef) groups fields)
    : groupsRepresentFields schema variableValues childRuntimeType childRuntimeType
        (.object childRuntimeType childRef)
        (candidateChildGroupsFor schema childParentType childRuntimeType traversal groups)
        (flattenCollectedFields
          (collectSubfields schema variableValues childRuntimeType
            (.object childRuntimeType childRef) fields)) := by
  intro childGroup hchildGroup
  simp only [candidateChildGroupsFor, List.mem_flatMap] at hchildGroup
  rcases hchildGroup with ⟨group, hgroup, hchildGroup⟩
  have hchildInherited := childInheritedBooleanCondition_allows variableValues group
    (hallows group hgroup) (hconditions group hgroup)
  have hshape := traversedCollectedGroup_shape childParentType
    group.childInheritedBooleanCondition
    (group.childTreeWithKnownFalsePruning schema childParentType traversal.summaryVariableValues)
    (traversal.atRuntimeType schema childRuntimeType) childGroup hchildGroup
  refine ⟨hshape.1, ?_⟩
  intro childSelection hchildSelection hchildCondition
  rcases traversedCollectedGroup_selection_producesField schema variableValues
      traversal.summaryVariableValues hmatch childParentType
      group.childInheritedBooleanCondition group.mergedSelectionSet
      childRuntimeType childRuntimeType childRef
      (traversal.atRuntimeType schema childRuntimeType) childGroup hchildInherited
      hpossible hchildGroup hchildCondition childSelection hchildSelection with
    ⟨childField, hchildInGroupMerged, hchildCover, hchildSelectionEq⟩
  have hchildFlat :
      childField ∈ collectFlatFields schema variableValues childRuntimeType
        (.object childRuntimeType childRef) group.mergedSelectionSet :=
    (collectFlatFields_mem_collectFields schema variableValues childRuntimeType
      (.object childRuntimeType childRef) group.mergedSelectionSet childField).mpr
      hchildInGroupMerged
  rcases collectFlatFields_mem_source schema variableValues childRuntimeType
      (.object childRuntimeType childRef) group.mergedSelectionSet childField hchildFlat with
    ⟨topChildSelection, htopMerged, hchildSingleton⟩
  rcases mergeSelectionSets_mem_source group.selections topChildSelection htopMerged with
    ⟨parentSelection, hparentSelection, htopSubselection⟩
  rcases hrepresent group hgroup with ⟨_hgroupFields, hrepresentSelections⟩
  rcases hrepresentSelections parentSelection hparentSelection
      (hconditions group hgroup) with
    ⟨parentField, hparentField, _hparentCover, hparentSelectionEq⟩
  have htopInParentField : topChildSelection ∈ parentField.selectionSet := by
    rw [hparentSelectionEq] at htopSubselection
    simpa [Selection.subselections] using htopSubselection
  have hchildInParentField :
      childField ∈ collectFlatFields schema variableValues childRuntimeType
        (.object childRuntimeType childRef) parentField.selectionSet := by
    exact collectFlatFields_mem_of_selection_mem schema variableValues childRuntimeType
      (.object childRuntimeType childRef) parentField.selectionSet topChildSelection
      childField htopInParentField hchildSingleton
  have htopInMergedFields :
      topChildSelection ∈ Execution.mergedFieldSelectionSet fields :=
    Algorithms.ExecutionUngrouped.selection_mem_mergedFieldSelectionSet_of_field_mem
      parentField fields hparentField topChildSelection htopInParentField
  have hchildInMergedFields :
      childField ∈ collectFlatFields schema variableValues childRuntimeType
        (.object childRuntimeType childRef)
        (Execution.mergedFieldSelectionSet fields) :=
    collectFlatFields_mem_of_selection_mem schema variableValues childRuntimeType
      (.object childRuntimeType childRef) (Execution.mergedFieldSelectionSet fields)
      topChildSelection childField htopInMergedFields hchildSingleton
  have hchildCollected :
      childField ∈ flattenCollectedFields
        (collectSubfields schema variableValues childRuntimeType
          (.object childRuntimeType childRef) fields) := by
    rw [NormalForm.collectSubfields_eq_collectFields_mergedFieldSelectionSet]
    exact (collectFlatFields_mem_collectFields schema variableValues childRuntimeType
      (.object childRuntimeType childRef) (Execution.mergedFieldSelectionSet fields)
      childField).mp hchildInMergedFields
  exact ⟨childField, hchildCollected, hchildCover, hchildSelectionEq⟩

theorem lookupField_outputType_mem_fieldOutputTypes_of_condition_allows
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

theorem lookupField_childParentType_mem_of_condition_allows
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
    lookupField_outputType_mem_fieldOutputTypes_of_condition_allows schema
      variableValues runtimeType group fieldName definition hallows hfieldName hlookup,
    rfl⟩

theorem summarizeCollectedChildren_append
    (algebra : Algebra.{v}) (lawful : algebra.Lawful)
    (schema : Schema) (traversal : Traversal)
    (left right : List CollectedFieldGroup)
    : summarizeCollectedChildren algebra schema traversal (left ++ right)
      = algebra.combine
          (summarizeCollectedChildren algebra schema traversal left)
          (summarizeCollectedChildren algebra schema traversal right) := by
  induction left with
  | nil =>
      simpa [summarizeCollectedChildren] using
        (lawful.empty_combine
          (summarizeCollectedChildren algebra schema traversal right)).symm
  | cons group rest ih =>
      simp only [List.cons_append, summarizeCollectedChildren]
      rw [ih, lawful.combine_assoc]

end Syntactic
end TreeSummary
end GraphQL
