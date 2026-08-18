import Proofs.GraphQL.Theories.QueryInclusion.ReferenceChecker
import Proofs.GraphQL.Theories.QueryInclusion.ErrorFreeExecution
import Proofs.GraphQL.Theories.SelectionConditions.Runtime
import Proofs.GraphQL.Algorithms.Common.SyntaxEq

/-! Shared proofs for type-region and Boolean-assignment query-inclusion search. -/

namespace GraphQL
namespace QueryInclusion

open Execution.FieldGroups

open Execution
open SelectionConditions
open Algorithms.ExecutionUngroupedUncached
open Algorithms.ExecutionUngroupedUncached.Eager

def BooleanAssignmentsAgree (knownValues complete : VariableValues) : Prop :=
  ∀ variableName value,
    inputValueBoolean? knownValues (.variable variableName) = some value
    -> inputValueBoolean? complete (.variable variableName) = some value

def BooleanVariablesCovered (knownValues : VariableValues)
    (remaining variables : List Name)
    : Prop :=
  ∀ variableName,
    variableName ∈ variables
    -> variableName ∈ remaining
        ∨ ∃ value, inputValueBoolean? knownValues (.variable variableName) = some value

theorem booleanAssignmentsAgree_nil (complete : VariableValues)
    : BooleanAssignmentsAgree [] complete := by
  intro variableName value hvalue
  simp [inputValueBoolean?, lookupVariableValue?] at hvalue

theorem booleanAssignmentsAgree_cons
    {knownValues complete : VariableValues} {variableName : Name} {value : Bool}
    (hagrees : BooleanAssignmentsAgree knownValues complete)
    (hvalue : inputValueBoolean? complete (.variable variableName) = some value)
    : BooleanAssignmentsAgree
        ((variableName, .boolean value) :: knownValues) complete := by
  intro candidate candidateValue hcandidate
  by_cases heq : variableName = candidate
  · subst candidate
    simp [inputValueBoolean?, lookupVariableValue?] at hcandidate
    cases hcandidate
    exact hvalue
  · simp [inputValueBoolean?, lookupVariableValue?, heq] at hcandidate
    exact hagrees candidate candidateValue hcandidate

theorem booleanVariablesCovered_tail_of_known
    {knownValues : VariableValues} {variableName : Name} {rest variables : List Name}
    (hcovered : BooleanVariablesCovered knownValues (variableName :: rest) variables)
    (hknown
      : ∃ value, inputValueBoolean? knownValues (.variable variableName) = some value)
    : BooleanVariablesCovered knownValues rest variables := by
  intro candidate hcandidate
  rcases hcovered candidate hcandidate with hremaining | hvalue
  · rcases List.mem_cons.mp hremaining with heq | hrest
    · subst candidate
      exact Or.inr hknown
    · exact Or.inl hrest
  · exact Or.inr hvalue

theorem booleanVariablesCovered_tail_of_cons
    {knownValues : VariableValues} {variableName : Name} {value : Bool}
    {rest variables : List Name}
    (hcovered : BooleanVariablesCovered knownValues (variableName :: rest) variables)
    : BooleanVariablesCovered
        ((variableName, .boolean value) :: knownValues) rest variables := by
  intro candidate hcandidate
  rcases hcovered candidate hcandidate with hremaining | hknown
  · rcases List.mem_cons.mp hremaining with heq | hrest
    · subst candidate
      exact Or.inr ⟨value, by
        simp [inputValueBoolean?, lookupVariableValue?, InputValue.staticBoolean?,
          ConstInputValue.toInputValue]⟩
    · exact Or.inl hrest
  · rcases hknown with ⟨candidateValue, hcandidateValue⟩
    by_cases heq : variableName = candidate
    · subst candidate
      exact Or.inr ⟨value, by
        simp [inputValueBoolean?, lookupVariableValue?, InputValue.staticBoolean?,
          ConstInputValue.toInputValue]⟩
    · exact Or.inr ⟨candidateValue, by
        simpa [inputValueBoolean?, lookupVariableValue?, heq] using hcandidateValue⟩

theorem executableGroupsWithParentType_addExecutableGroup
    (parentType : Name) (group : Name × List ExecutableField)
    (groups : List (Name × List ExecutableField))
    : executableGroupsWithParentType parentType (addExecutableGroup group groups)
      = addExecutableGroup (executableGroupWithParentType parentType group)
          (executableGroupsWithParentType parentType groups) := by
  induction groups with
  | nil => simp [executableGroupsWithParentType, executableGroupWithParentType,
      addExecutableGroup]
  | cons candidate rest ih =>
      rcases candidate with ⟨responseName, fields⟩
      rcases group with ⟨groupName, groupFields⟩
      rw [addExecutableGroup]
      split <;> rename_i hname
      · unfold executableGroupsWithParentType executableGroupWithParentType
        simp [List.map_append, addExecutableGroup, hname]
      · unfold executableGroupsWithParentType executableGroupWithParentType at ih ⊢
        simp [addExecutableGroup, hname, ih]

theorem executableGroupsWithParentType_groupExecutableFields_acc
    (parentType : Name) (fields : List ExecutableField)
    (groups : List (Name × List ExecutableField))
    : executableGroupsWithParentType parentType
        (fields.foldl
          (fun accumulated field =>
            addExecutableGroup (field.responseName, [field]) accumulated)
          groups)
      = (fields.map (executableFieldWithParentType parentType)).foldl
          (fun accumulated field =>
            addExecutableGroup (field.responseName, [field]) accumulated)
          (executableGroupsWithParentType parentType groups) := by
  induction fields generalizing groups with
  | nil => rfl
  | cons field rest ih =>
      simp only [List.foldl_cons, List.map_cons]
      rw [ih, executableGroupsWithParentType_addExecutableGroup]
      rfl

theorem executableGroupsWithParentType_groupExecutableFields
    (parentType : Name) (fields : List ExecutableField)
    : executableGroupsWithParentType parentType (groupExecutableFields fields)
      = groupExecutableFields
          (fields.map (executableFieldWithParentType parentType)) := by
  exact executableGroupsWithParentType_groupExecutableFields_acc parentType fields []

theorem selectionConditionsForRegion_runtimeGroups_permutationEquivalent
    {ObjectRef : Type}
    (schema : Schema) (region : List Name)
    {extractedSelectionSet targetSelectionSet : List Selection}
    (hselectionSet : extractedSelectionSet.Perm targetSelectionSet)
    (variableValues : VariableValues) (executionParentType runtimeType : Name)
    (ref : ObjectRef) (hruntime : runtimeType ∈ region)
    : RuntimeGroupsPermutationEquivalent
        (groupExecutableFields
          (SelectionConditions.runtimeFields variableValues executionParentType
            runtimeType
            (SelectionConditions.ofTypeRegion schema region extractedSelectionSet)))
        (collectFields schema variableValues executionParentType
          (.object runtimeType ref) targetSelectionSet) := by
  let condition : SelectionConditions.Condition :=
    { possibleTypes := region, booleanCondition := [] }
  have hroot : condition.allows variableValues runtimeType = true := by
    simp [condition, SelectionConditions.Condition.allows, hruntime,
      SelectionConditions.booleanConditionAllows]
  have hsource := SelectionConditions.extractFields_runtimeFields schema
    variableValues executionParentType runtimeType ref [] condition
    extractedSelectionSet (by simp [SelectionConditions.booleanConditionAllows])
  rw [hroot] at hsource
  simp only [if_true] at hsource
  have hfields :
      SelectionConditions.runtimeFields variableValues executionParentType runtimeType
          (SelectionConditions.ofTypeRegion schema region extractedSelectionSet)
        =
          (collectFlatFields schema variableValues executionParentType
            (.object runtimeType ref) extractedSelectionSet) := by
    exact hsource
  let fields := SelectionConditions.runtimeFields variableValues executionParentType
    runtimeType (SelectionConditions.ofTypeRegion schema region extractedSelectionSet)
  have hgrouped := groupExecutableFields_exact fields
  constructor
  · exact groupExecutableFields_wellFormed fields
  · exact NormalForm.GroundTypeNormalization.collectFields_wellFormed schema
      variableValues executionParentType (.object runtimeType ref) targetSelectionSet
  · exact hgrouped.1
  · exact (executableGroupNamesNodup_iff_map_fst_nodup _).mp
      (NormalForm.collectFields_namesNodup schema variableValues executionParentType
        (.object runtimeType ref) targetSelectionSet)
  · rw [← Execution.FieldGroups.flattenCollectedFields_eq_flatMap_snd,
      ← Execution.FieldGroups.flattenCollectedFields_eq_flatMap_snd]
    apply hgrouped.2.trans
    apply (List.Perm.of_eq hfields).trans
    apply (collectFlatFields_perm_of_selectionSet_perm
      schema variableValues executionParentType (.object runtimeType ref)
      hselectionSet).trans
    exact collectFlatFields_perm_flatten_collectFields
      schema variableValues executionParentType (.object runtimeType ref)
      targetSelectionSet

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

theorem runtimeGroupsPermutationEquivalent_matchingGroup
    {left right : List (Name × List ExecutableField)}
    (equivalent : RuntimeGroupsPermutationEquivalent left right)
    {responseName : Name} {leftFields : List ExecutableField}
    (hleft : (responseName, leftFields) ∈ left)
    : ∃ rightFields,
        (responseName, rightFields) ∈ right ∧ leftFields.Perm rightFields := by
  rcases List.mem_iff_append.mp hleft with ⟨before, after, hleftList⟩
  subst left
  let leftTail := before ++ after
  have hperm :
      (before ++ (responseName, leftFields) :: after).Perm
        ((responseName, leftFields) :: leftTail) := by
    simp [leftTail]
  have reordered := runtimeGroupsPermutationEquivalent_permuteLeft equivalent hperm
  rcases reordered.alignRightHead with
    ⟨rightFields, rightTail, hrightPerm, aligned⟩
  refine ⟨rightFields, ?_, aligned.headFields⟩
  exact hrightPerm.mem_iff.mpr (by simp)

theorem runtimeGroupsPermutationEquivalent_isEmpty_iff
    {left right : List (Name × List ExecutableField)}
    (equivalent : RuntimeGroupsPermutationEquivalent left right)
    : left.isEmpty = right.isEmpty := by
  cases left with
  | nil =>
      cases right with
      | nil => rfl
      | cons group rest =>
          have hkey : group.1 ∈ ((group :: rest).map Prod.fst) := by simp
          have := (equivalent.keys group.1).mpr hkey
          simp at this
  | cons group rest =>
      cases right with
      | nil =>
          have hkey : group.1 ∈ ((group :: rest).map Prod.fst) := by simp
          have := (equivalent.keys group.1).mp hkey
          simp at this
      | cons => rfl

def executableGroupsResolverReady (groups : List (Name × List ExecutableField)) : Prop :=
  ∀ responseName fields,
    (responseName, fields) ∈ groups -> fields ≠ [] ∧ executableFieldsSameResolver fields

def executableFieldSemanticsReady (schema : Schema) (field : ExecutableField) : Prop :=
  ∃ definition,
    schema.lookupField field.parentType field.fieldName = some definition
    ∧ ∀ runtimeType,
        schema.typeIncludesObjectBool definition.outputType.namedType runtimeType = true
        -> NormalForm.selectionSetSemanticsReady schema runtimeType field.selectionSet

def executableFieldsSemanticsReady (schema : Schema) (fields : List ExecutableField)
    : Prop :=
  fields ≠ []
  ∧ (∀ field, field ∈ fields -> executableFieldSemanticsReady schema field)
  ∧ executableFieldsSameResolver fields
  ∧ ∀ objectType,
      FieldMerge.fieldsInSetCanMerge schema objectType (mergedFieldSelectionSet fields)

def executableGroupsSemanticsReady (schema : Schema)
    (groups : List (Name × List ExecutableField))
    : Prop :=
  ∀ responseName fields,
    (responseName, fields) ∈ groups -> executableFieldsSemanticsReady schema fields

theorem executableGroupsSemanticsReady_of_ready
    {schema : Schema} {groups : List (Name × List ExecutableField)}
    (hready : executableGroupsReady schema groups)
    : executableGroupsSemanticsReady schema groups := by
  intro responseName fields hgroup
  have hfields := hready responseName fields hgroup
  refine ⟨hfields.1, ?_, hfields.2.2.1, hfields.2.2.2⟩
  intro field hfield
  rcases hfields.2.1 field hfield with
    ⟨definition, hlookup, hchild, _hinhabited⟩
  exact ⟨definition, hlookup, hchild⟩

def completionFieldsWitness (schema : Schema) (fieldType : TypeRef)
    (fields : List ExecutableField)
    : Prop :=
  ∃ field definition,
    field ∈ fields
    ∧ schema.lookupField field.parentType field.fieldName = some definition
    ∧ fieldType.namedType = definition.outputType.namedType

def completionFieldsSemanticsReady (schema : Schema) (fieldType : TypeRef)
    (fields : List ExecutableField)
    : Prop :=
  executableFieldsSemanticsReady schema fields
  ∧ completionFieldsWitness schema fieldType fields

theorem executableGroupsResolverReady_of_semanticsReady
    {schema : Schema} {groups : List (Name × List ExecutableField)}
    (hready : executableGroupsSemanticsReady schema groups)
    : executableGroupsResolverReady groups := by
  intro responseName fields hgroup
  have hfields := hready responseName fields hgroup
  exact ⟨hfields.1, hfields.2.2.1⟩

theorem executableGroupsSemanticsReady_collectFields
    (schema : Schema) (variableValues : VariableValues)
    (parentType : Name) (ref : ObjectRef) (selectionSet : List Selection)
    (hobject : schema.objectType parentType)
    (hready : NormalForm.selectionSetSemanticsReady schema parentType selectionSet)
    (hmerge : FieldMerge.fieldsInSetCanMerge schema parentType selectionSet)
    : executableGroupsSemanticsReady schema
        (collectFields schema variableValues parentType (.object parentType ref)
          selectionSet) := by
  let groups :=
    collectFields schema variableValues parentType (.object parentType ref) selectionSet
  have hself : ScopedParentRuntimeApplies schema parentType parentType :=
    NormalForm.object_typeIncludesObjectBool_self schema hobject
  have hnonempty : CollectedGroupsFieldsNonempty groups := by
    exact collectFields_fieldsNonempty schema variableValues parentType
      (.object parentType ref) selectionSet
  have hparents : CollectedGroupsParent parentType groups := by
    exact collectFields_parent schema variableValues parentType
      (.object parentType ref) selectionSet
  have hlookup :=
    collectFields_lookupValid_of_selectionSetSemanticsReady_object schema
      variableValues parentType parentType ref selectionSet hobject hself hready
  have hchild :=
    collectFields_childSemanticsReady_of_selectionSetSemanticsReady_object schema
      variableValues parentType parentType ref selectionSet hobject hself hready
  have hresponses : CollectedGroupsResponseName groups := by
    exact collectFields_responseName schema variableValues parentType
      (.object parentType ref) selectionSet
  have hcompatible : CollectedGroupsFieldValidationMergeCompatible groups := by
    dsimp only [groups]
    exact collectFields_fieldCompatible_of_canMerge_lookupValid_object schema
      variableValues parentType parentType parentType ref selectionSet hmerge hself
      (NormalForm.selectionSetLookupValid_of_selectionSetSemanticsReady selectionSet
        hready)
  have hscoped :
      ExecutableFieldsRuntimeScopedBy schema parentType
        (FieldMerge.collectFields schema parentType selectionSet)
        (collectedExecutableFields groups) := by
    dsimp only [groups]
    exact collectFields_runtimeScopedBy_of_selectionSetLookupValid_object schema
      variableValues parentType parentType parentType ref selectionSet hself
      (NormalForm.selectionSetLookupValid_of_selectionSetSemanticsReady selectionSet
        hready)
  intro responseName fields hgroup
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact hnonempty responseName fields hgroup
  · intro field hfield
    have hparent : field.parentType = parentType :=
      hparents responseName fields hgroup field hfield
    have hflat : field ∈ collectedExecutableFields groups :=
      collectedExecutableFields_mem_of_group_mem hgroup hfield
    rcases hlookup field hflat with ⟨definition, hdefinition⟩
    refine ⟨definition, by simpa [hparent] using hdefinition, ?_⟩
    intro runtimeType hincludes
    exact hchild field hflat definition (by simpa [hparent] using hdefinition)
      runtimeType hincludes
  · intro first later hfirst hlater
    have hparent : first.parentType = later.parentType := by
      rw [hparents responseName fields hgroup first hfirst,
        hparents responseName fields hgroup later hlater]
    have hresponse : first.responseName = later.responseName := by
      rw [hresponses responseName fields hgroup first hfirst,
        hresponses responseName fields hgroup later hlater]
    exact ⟨hparent,
      hcompatible responseName fields hgroup first later hfirst hlater hresponse⟩
  · intro objectType
    apply fieldsInSetCanMerge_mergedFieldSelectionSet_of_runtimeScoped schema
      parentType parentType selectionSet responseName fields hmerge
    · exact hresponses responseName fields hgroup
    · intro field hfield
      exact hscoped field
        (collectedExecutableFields_mem_of_group_mem hgroup hfield)

theorem completionFieldsSemanticsReady_merged_semantics
    {schema : Schema} {fieldType : TypeRef} {fields : List ExecutableField}
    {runtimeType : Name}
    (hready : completionFieldsSemanticsReady schema fieldType fields)
    (hincludes : schema.typeIncludesObjectBool fieldType.namedType runtimeType = true)
    : NormalForm.selectionSetSemanticsReady schema runtimeType
        (mergedFieldSelectionSet fields) := by
  rcases hready with
    ⟨hfieldsReady, sourceField, sourceDefinition, hsource, hsourceLookup, htype⟩
  have heach : ∀ field, field ∈ fields ->
      NormalForm.selectionSetSemanticsReady schema runtimeType field.selectionSet := by
    intro field hfield
    rcases hfieldsReady.2.1 field hfield with
      ⟨fieldDefinition, hfieldLookup, hchild⟩
    rcases hfieldsReady.2.2.1 sourceField field hsource hfield with
      ⟨hparent, hfieldName, _harguments⟩
    have hfieldLookup' :
        schema.lookupField sourceField.parentType sourceField.fieldName
          = some fieldDefinition := by
      simpa [hparent, hfieldName] using hfieldLookup
    rw [hsourceLookup] at hfieldLookup'
    injection hfieldLookup' with hdefinition
    subst fieldDefinition
    apply hchild runtimeType
    rw [← htype]
    exact hincludes
  have hflat : ∀ candidates : List ExecutableField,
      (∀ field, field ∈ candidates ->
        NormalForm.selectionSetSemanticsReady schema runtimeType field.selectionSet)
      -> NormalForm.selectionSetSemanticsReady schema runtimeType
          (candidates.flatMap ExecutableField.selectionSet) := by
    intro candidates
    induction candidates with
    | nil =>
        intro _hready
        exact NormalForm.selectionSetSemanticsReady_nil schema runtimeType
    | cons field rest ih =>
        intro hcandidates
        rw [List.flatMap_cons]
        apply NormalForm.selectionSetSemanticsReady_append
        · exact hcandidates field (by simp)
        · apply ih
          intro candidate hcandidate
          exact hcandidates candidate (by simp [hcandidate])
  rw [Execution.FieldGroups.mergedFieldSelectionSet_eq_flatMap]
  exact hflat fields heach

theorem completionFieldsSemanticsReady_merged_canMerge
    {schema : Schema} {fieldType : TypeRef} {fields : List ExecutableField}
    (hready : completionFieldsSemanticsReady schema fieldType fields)
    (objectType : Name)
    : FieldMerge.fieldsInSetCanMerge schema objectType (mergedFieldSelectionSet fields) :=
  hready.1.2.2.2 objectType

theorem executableGroupsResolverReady_of_permutationEquivalent
    {guardedGroups runtimeGroups : List (Name × List ExecutableField)}
    (equivalent : RuntimeGroupsPermutationEquivalent guardedGroups runtimeGroups)
    (hruntimeReady : executableGroupsResolverReady runtimeGroups)
    : executableGroupsResolverReady guardedGroups := by
  intro responseName guardedFields hguardedGroup
  rcases runtimeGroupsPermutationEquivalent_matchingGroup equivalent hguardedGroup with
    ⟨runtimeFields, hruntimeGroup, hfieldsPerm⟩
  have hruntime := hruntimeReady responseName runtimeFields hruntimeGroup
  refine ⟨?_, ?_⟩
  · intro hempty
    subst guardedFields
    have := hfieldsPerm.length_eq
    exact hruntime.1 (List.eq_nil_of_length_eq_zero (by simpa using this.symm))
  · intro first later hfirst hlater
    exact hruntime.2 first later (hfieldsPerm.mem_iff.mp hfirst)
      (hfieldsPerm.mem_iff.mp hlater)

theorem executableGroupsIncludeBool_transport
    (schema : Schema)
    (guardedChildIncludes runtimeChildIncludes
      : TypeRef -> List Selection -> List Selection -> Bool)
    (guardedLeftGroups guardedRightGroups runtimeLeftGroups runtimeRightGroups
      : List (Name × List ExecutableField))
    (hleftEquivalent
      : RuntimeGroupsPermutationEquivalent guardedLeftGroups runtimeLeftGroups)
    (hrightEquivalent
      : RuntimeGroupsPermutationEquivalent guardedRightGroups runtimeRightGroups)
    (hruntimeLeftReady : executableGroupsResolverReady runtimeLeftGroups)
    (hruntimeRightReady : executableGroupsResolverReady runtimeRightGroups)
    (hchild
      : ∀ fieldType leftName rightName guardedLeftFields runtimeLeftFields
          guardedRightFields runtimeRightFields,
          (leftName, guardedLeftFields) ∈ guardedLeftGroups
          -> (leftName, runtimeLeftFields) ∈ runtimeLeftGroups
          -> (rightName, guardedRightFields) ∈ guardedRightGroups
          -> (rightName, runtimeRightFields) ∈ runtimeRightGroups
          -> leftName = rightName
          -> guardedLeftFields.Perm runtimeLeftFields
          -> guardedRightFields.Perm runtimeRightFields
          -> completionFieldsWitness schema fieldType guardedLeftFields
          -> completionFieldsWitness schema fieldType runtimeLeftFields
          -> completionFieldsWitness schema fieldType guardedRightFields
          -> completionFieldsWitness schema fieldType runtimeRightFields
          -> guardedChildIncludes fieldType
                (executableFieldsMergedSelectionSet guardedLeftFields)
                (executableFieldsMergedSelectionSet guardedRightFields)
              = true
          -> runtimeChildIncludes fieldType
                (executableFieldsMergedSelectionSet runtimeLeftFields)
                (executableFieldsMergedSelectionSet runtimeRightFields)
              = true)
    (hinclude
      : executableGroupsIncludeBool schema guardedChildIncludes guardedLeftGroups
          guardedRightGroups
        = true)
    : executableGroupsIncludeBool schema runtimeChildIncludes runtimeLeftGroups
        runtimeRightGroups
      = true := by
  apply List.all_eq_true.mpr
  intro runtimeRightGroup hruntimeRightGroup
  rcases runtimeRightGroup with ⟨rightName, runtimeRightFields⟩
  rcases runtimeGroupsPermutationEquivalent_matchingGroup
      (runtimeGroupsPermutationEquivalent_symm hrightEquivalent) hruntimeRightGroup with
    ⟨guardedRightFields, hguardedRightGroup, hrightFieldsPerm⟩
  have hrightFieldsPerm' : guardedRightFields.Perm runtimeRightFields :=
    hrightFieldsPerm.symm
  have hguardedIncluded := List.all_eq_true.mp hinclude
    (rightName, guardedRightFields) hguardedRightGroup
  unfold executableGroupIncludedBool at hguardedIncluded ⊢
  rcases List.any_eq_true.mp hguardedIncluded with
    ⟨guardedLeftGroup, hguardedLeftGroup, hguardedMatch⟩
  rcases guardedLeftGroup with ⟨leftName, guardedLeftFields⟩
  rcases runtimeGroupsPermutationEquivalent_matchingGroup hleftEquivalent
      hguardedLeftGroup with ⟨runtimeLeftFields, hruntimeLeftGroup, hleftFieldsPerm⟩
  apply List.any_eq_true.mpr
  refine ⟨(leftName, runtimeLeftFields), hruntimeLeftGroup, ?_⟩
  have hruntimeLeftFieldsReady := hruntimeLeftReady leftName runtimeLeftFields hruntimeLeftGroup
  have hruntimeRightFieldsReady := hruntimeRightReady rightName runtimeRightFields hruntimeRightGroup
  cases hguardedLeftFields : guardedLeftFields with
  | nil =>
      subst guardedLeftFields
      simp at hguardedMatch
  | cons guardedLeftHead guardedLeftRest =>
      cases hguardedRightFields : guardedRightFields with
      | nil =>
          subst guardedRightFields
          simp at hguardedMatch
      | cons guardedRightHead guardedRightRest =>
          cases hruntimeLeftFields : runtimeLeftFields with
          | nil => exact False.elim (hruntimeLeftFieldsReady.1 hruntimeLeftFields)
          | cons runtimeLeftHead runtimeLeftRest =>
              cases hruntimeRightFields : runtimeRightFields with
              | nil => exact False.elim (hruntimeRightFieldsReady.1 hruntimeRightFields)
              | cons runtimeRightHead runtimeRightRest =>
                  subst guardedLeftFields
                  subst guardedRightFields
                  subst runtimeLeftFields
                  subst runtimeRightFields
                  have hleftGuardedMember : guardedLeftHead ∈ runtimeLeftHead :: runtimeLeftRest :=
                    hleftFieldsPerm.mem_iff.mp (by simp)
                  have hrightGuardedMember : guardedRightHead ∈ runtimeRightHead :: runtimeRightRest :=
                    hrightFieldsPerm'.mem_iff.mp (by simp)
                  rcases hruntimeLeftFieldsReady.2 guardedLeftHead runtimeLeftHead
                      hleftGuardedMember (by simp) with
                    ⟨hleftParent, hleftField, hleftArguments⟩
                  rcases hruntimeRightFieldsReady.2 guardedRightHead runtimeRightHead
                      hrightGuardedMember (by simp) with
                    ⟨hrightParent, hrightField, hrightArguments⟩
                  simp only [Bool.and_eq_true] at hguardedMatch
                  have hname := hguardedMatch.1
                  have hcall := hguardedMatch.2.1
                  have hguardedParent := hcall.1.1
                  have hguardedField := hcall.1.2
                  have hguardedArguments := hcall.2
                  have hguardedChild := hguardedMatch.2.2
                  have hruntimeParent : runtimeLeftHead.parentType = runtimeRightHead.parentType :=
                    hleftParent.symm.trans (beq_iff_eq.mp hguardedParent)
                      |>.trans hrightParent
                  have hruntimeField : runtimeLeftHead.fieldName = runtimeRightHead.fieldName :=
                    hleftField.symm.trans (beq_iff_eq.mp hguardedField)
                      |>.trans hrightField
                  have hruntimeArguments : Argument.argumentsEquivalent
                      runtimeLeftHead.arguments runtimeRightHead.arguments :=
                    argumentsEquivalent_trans
                      (FieldMerge.argumentsEquivalent_symm hleftArguments)
                      (argumentsEquivalent_trans
                        ((argumentsSyntacticallyEquivalentBool_iff _ _).mp hguardedArguments)
                        hrightArguments)
                  simp only [Bool.and_eq_true]
                  refine ⟨hname,
                    ⟨⟨beq_iff_eq.mpr hruntimeParent, beq_iff_eq.mpr hruntimeField⟩,
                      (argumentsSyntacticallyEquivalentBool_iff _ _).mpr hruntimeArguments⟩, ?_⟩
                  have hlookup : schema.lookupField runtimeRightHead.parentType
                      runtimeRightHead.fieldName
                    = schema.lookupField guardedRightHead.parentType
                        guardedRightHead.fieldName := by
                    rw [hrightParent, hrightField]
                  rw [hlookup]
                  cases hdefinition
                        : schema.lookupField guardedRightHead.parentType
                            guardedRightHead.fieldName with
                  | none => simp [hdefinition] at hguardedChild
                  | some definition =>
                      cases hcomposite : definition.outputType.isCompositeBool schema with
                      | false => simp [hcomposite]
                      | true =>
                          simp only [hdefinition, hcomposite, if_true] at hguardedChild ⊢
                          have hguardedRightLookup : schema.lookupField
                              guardedRightHead.parentType guardedRightHead.fieldName
                            = some definition := hdefinition
                          have hruntimeRightLookup : schema.lookupField
                              runtimeRightHead.parentType runtimeRightHead.fieldName
                            = some definition := by
                            rw [hlookup, hdefinition]
                          have hguardedLeftLookup : schema.lookupField
                              guardedLeftHead.parentType guardedLeftHead.fieldName
                            = some definition := by
                            simpa [beq_iff_eq.mp hguardedParent,
                              beq_iff_eq.mp hguardedField] using hdefinition
                          have hruntimeLeftLookup : schema.lookupField
                              runtimeLeftHead.parentType runtimeLeftHead.fieldName
                            = some definition := by
                            simpa [hruntimeParent, hruntimeField] using hruntimeRightLookup
                          exact hchild definition.outputType leftName rightName
                            (guardedLeftHead :: guardedLeftRest)
                            (runtimeLeftHead :: runtimeLeftRest)
                            (guardedRightHead :: guardedRightRest)
                            (runtimeRightHead :: runtimeRightRest)
                            hguardedLeftGroup hruntimeLeftGroup hguardedRightGroup hruntimeRightGroup
                            (beq_iff_eq.mp hname) hleftFieldsPerm hrightFieldsPerm'
                            ⟨guardedLeftHead, definition, by simp, hguardedLeftLookup, rfl⟩
                            ⟨runtimeLeftHead, definition, by simp, hruntimeLeftLookup, rfl⟩
                            ⟨guardedRightHead, definition, by simp, hguardedRightLookup, rfl⟩
                            ⟨runtimeRightHead, definition, by simp, hruntimeRightLookup, rfl⟩
                            hguardedChild

theorem executableGroupsIncludeBool_transport_of_ready
    (schema : Schema)
    (guardedChildIncludes runtimeChildIncludes
      : TypeRef -> List Selection -> List Selection -> Bool)
    (guardedLeftGroups guardedRightGroups runtimeLeftGroups runtimeRightGroups
      : List (Name × List ExecutableField))
    (hleftEquivalent
      : RuntimeGroupsPermutationEquivalent guardedLeftGroups runtimeLeftGroups)
    (hrightEquivalent
      : RuntimeGroupsPermutationEquivalent guardedRightGroups runtimeRightGroups)
    (hruntimeLeftReady : executableGroupsSemanticsReady schema runtimeLeftGroups)
    (hruntimeRightReady : executableGroupsSemanticsReady schema runtimeRightGroups)
    (hchild
      : ∀ fieldType leftName rightName runtimeLeftFields guardedLeftFields
          runtimeRightFields guardedRightFields,
          (leftName, runtimeLeftFields) ∈ runtimeLeftGroups
          -> (leftName, guardedLeftFields) ∈ guardedLeftGroups
          -> (rightName, runtimeRightFields) ∈ runtimeRightGroups
          -> (rightName, guardedRightFields) ∈ guardedRightGroups
          -> leftName = rightName
          -> runtimeLeftFields.Perm guardedLeftFields
          -> runtimeRightFields.Perm guardedRightFields
          -> completionFieldsWitness schema fieldType runtimeLeftFields
          -> completionFieldsWitness schema fieldType guardedLeftFields
          -> completionFieldsWitness schema fieldType runtimeRightFields
          -> completionFieldsWitness schema fieldType guardedRightFields
          -> runtimeChildIncludes fieldType
                (executableFieldsMergedSelectionSet runtimeLeftFields)
                (executableFieldsMergedSelectionSet runtimeRightFields)
              = true
          -> guardedChildIncludes fieldType
                (executableFieldsMergedSelectionSet guardedLeftFields)
                (executableFieldsMergedSelectionSet guardedRightFields)
              = true)
    (hinclude
      : executableGroupsIncludeBool schema runtimeChildIncludes runtimeLeftGroups
          runtimeRightGroups
        = true)
    : executableGroupsIncludeBool schema guardedChildIncludes guardedLeftGroups
        guardedRightGroups
      = true := by
  apply executableGroupsIncludeBool_transport schema runtimeChildIncludes
    guardedChildIncludes runtimeLeftGroups runtimeRightGroups guardedLeftGroups guardedRightGroups
    (runtimeGroupsPermutationEquivalent_symm hleftEquivalent)
    (runtimeGroupsPermutationEquivalent_symm hrightEquivalent)
  · exact executableGroupsResolverReady_of_permutationEquivalent hleftEquivalent
      (executableGroupsResolverReady_of_semanticsReady hruntimeLeftReady)
  · exact executableGroupsResolverReady_of_permutationEquivalent hrightEquivalent
      (executableGroupsResolverReady_of_semanticsReady hruntimeRightReady)
  · exact hchild
  · exact hinclude

theorem selectionSetBooleanVariables_eq_flatMap (selectionSet : List Selection)
    : SelectionConditions.selectionSetBooleanVariables selectionSet
      = selectionSet.flatMap SelectionConditions.selectionBooleanVariables := by
  induction selectionSet with
  | nil => rfl
  | cons selection rest tail_ih =>
      simp [SelectionConditions.selectionSetBooleanVariables, tail_ih]

theorem selectionSetBooleanVariables_perm
    {left right : List Selection} (hselectionSet : left.Perm right)
    : (SelectionConditions.selectionSetBooleanVariables left).Perm
        (SelectionConditions.selectionSetBooleanVariables right) := by
  rw [selectionSetBooleanVariables_eq_flatMap,
    selectionSetBooleanVariables_eq_flatMap]
  exact List.Perm.flatMap hselectionSet
    SelectionConditions.selectionBooleanVariables

theorem matchInclusionChildTask?_sound (schema : Schema)
    (childIncludes : List Name -> List Selection -> List Selection -> Bool)
    (rightGroup : Name × List ExecutableField)
    (leftGroups : List (Name × List ExecutableField)) (task : InclusionChildMatch)
    (hmatch : matchInclusionChildTask? schema rightGroup leftGroups = some task)
    (htask
      : ∀ childTask,
          task = .composite childTask
          -> childIncludes childTask.possibleTypes childTask.leftSelectionSet
                childTask.rightSelectionSet
              = true)
    : leftGroups.any
        fun leftGroup =>
          leftGroup.1 == rightGroup.1
          && match leftGroup.2, rightGroup.2 with
              | leftField :: _, rightField :: _ =>
                  leftField.parentType == rightField.parentType
                  && leftField.fieldName == rightField.fieldName
                  && Argument.argumentsSyntacticallyEquivalentBool leftField.arguments
                      rightField.arguments
                  && match schema.lookupField rightField.parentType
                            rightField.fieldName with
                      | none => false
                      | some definition =>
                          if definition.outputType.isCompositeBool schema then
                            childIncludes
                              (schema.getPossibleTypes definition.outputType.namedType)
                              (executableFieldsMergedSelectionSet leftGroup.2)
                              (executableFieldsMergedSelectionSet rightGroup.2)
                          else
                            true
              | _, _ => false := by
  induction leftGroups generalizing task with
  | nil => simp [matchInclusionChildTask?] at hmatch
  | cons leftGroup rest ih =>
      rcases leftGroup with ⟨leftName, leftFields⟩
      rcases rightGroup with ⟨rightName, rightFields⟩
      rw [matchInclusionChildTask?] at hmatch
      rw [List.any_cons]
      cases hname : leftName == rightName with
      | false =>
          simp only [hname, Bool.false_eq_true, if_false] at hmatch ⊢
          exact ih task hmatch htask
      | true =>
          simp only [hname, if_true] at hmatch ⊢
          cases leftFields with
          | nil =>
              simp only [Bool.and_false, Bool.false_or]
              exact ih task (by simpa using hmatch) htask
          | cons leftField leftRest =>
              cases rightFields with
              | nil =>
                  simp only [Bool.and_false, Bool.false_or]
                  exact ih task (by simpa using hmatch) htask
              | cons rightField rightRest =>
                  let compatible :=
                    leftField.parentType == rightField.parentType
                    && leftField.fieldName == rightField.fieldName
                    && Argument.argumentsSyntacticallyEquivalentBool leftField.arguments
                      rightField.arguments
                  cases hcompatible : compatible with
                  | false =>
                      simp only [compatible, hcompatible, Bool.false_eq_true, if_false]
                        at hmatch ⊢
                      exact ih task hmatch htask
                  | true =>
                      simp only [compatible, hcompatible, if_true] at hmatch ⊢
                      cases hlookup
                            : schema.lookupField rightField.parentType
                                rightField.fieldName with
                      | none => simp [hlookup] at hmatch
                      | some definition =>
                          cases hcomposite
                                : definition.outputType.isCompositeBool schema with
                          | false =>
                              simp [hlookup, hcomposite] at hmatch ⊢
                          | true =>
                              have htaskEq : task = .composite {
                                  possibleTypes := schema.getPossibleTypes
                                    definition.outputType.namedType
                                  leftSelectionSet := executableFieldsMergedSelectionSet
                                    (leftField :: leftRest)
                                  rightSelectionSet := executableFieldsMergedSelectionSet
                                    (rightField :: rightRest) } := by
                                simpa [hlookup, hcomposite] using hmatch.symm
                              have hchild := htask _ htaskEq
                              simp only [hcomposite, if_true, Bool.true_and,
                                Bool.or_eq_true]
                              exact Or.inl (by
                                simpa [hcomposite] using hchild)

theorem executableGroupIncludedBool_eq_false_of_name_not_mem
    (schema : Schema)
    (childIncludes : TypeRef -> List Selection -> List Selection -> Bool)
    (leftGroups : List (Name × List ExecutableField))
    (rightGroup : Name × List ExecutableField)
    (hname : rightGroup.1 ∉ leftGroups.map Prod.fst)
    : executableGroupIncludedBool schema childIncludes leftGroups rightGroup = false := by
  unfold executableGroupIncludedBool
  apply List.any_eq_false.mpr
  intro leftGroup hleft hincluded
  rw [Bool.and_eq_true] at hincluded
  have heq : leftGroup.1 = rightGroup.1 :=
    beq_iff_eq.mp hincluded.1
  apply hname
  exact List.mem_map.mpr ⟨leftGroup, hleft, heq⟩

theorem matchInclusionChildTask?_child_true
    (schema : Schema)
    (childIncludes : List Name -> List Selection -> List Selection -> Bool)
    (rightGroup : Name × List ExecutableField)
    (leftGroups : List (Name × List ExecutableField)) (task : InclusionChildTask)
    (hnodup : (leftGroups.map Prod.fst).Nodup)
    (hmatch
      : matchInclusionChildTask? schema rightGroup leftGroups = some (.composite task))
    (hinclude
      : executableGroupIncludedBool schema
          (fun outputType => childIncludes (schema.getPossibleTypes outputType.namedType))
          leftGroups rightGroup
        = true)
    : childIncludes task.possibleTypes task.leftSelectionSet task.rightSelectionSet
      = true := by
  induction leftGroups generalizing task with
  | nil => simp [matchInclusionChildTask?] at hmatch
  | cons leftGroup rest ih =>
      rcases leftGroup with ⟨leftName, leftFields⟩
      rcases rightGroup with ⟨rightName, rightFields⟩
      rw [matchInclusionChildTask?] at hmatch
      unfold executableGroupIncludedBool at hinclude
      simp only [List.any_cons] at hinclude
      have hnodupParts := List.nodup_cons.mp hnodup
      cases hname : leftName == rightName with
      | false =>
          simp only [hname, Bool.false_eq_true, if_false] at hmatch hinclude
          exact ih task hnodupParts.2 hmatch hinclude
      | true =>
          simp only [hname, if_true, Bool.true_and] at hmatch hinclude
          cases leftFields with
          | nil =>
              simp only [Bool.false_or] at hinclude
              exact ih task hnodupParts.2 (by simpa using hmatch) hinclude
          | cons leftField leftRest =>
              cases rightFields with
              | nil =>
                  simp only [Bool.false_or] at hinclude
                  exact ih task hnodupParts.2 (by simpa using hmatch) hinclude
              | cons rightField rightRest =>
                  let compatible :=
                    leftField.parentType == rightField.parentType
                    && leftField.fieldName == rightField.fieldName
                    && Argument.argumentsSyntacticallyEquivalentBool leftField.arguments
                      rightField.arguments
                  cases hcompatible : compatible with
                  | false =>
                      simp only [compatible, hcompatible, Bool.false_eq_true, if_false]
                        at hmatch hinclude
                      exact ih task hnodupParts.2 hmatch hinclude
                  | true =>
                      simp only [compatible, hcompatible, if_true] at hmatch hinclude
                      cases hlookup
                            : schema.lookupField rightField.parentType
                                rightField.fieldName with
                      | none => simp [hlookup] at hmatch
                      | some definition =>
                          cases hcomposite
                                : definition.outputType.isCompositeBool schema with
                          | false => simp [hlookup, hcomposite] at hmatch
                          | true =>
                              have htask : task = {
                                  possibleTypes := schema.getPossibleTypes
                                    definition.outputType.namedType
                                  leftSelectionSet := executableFieldsMergedSelectionSet
                                    (leftField :: leftRest)
                                  rightSelectionSet := executableFieldsMergedSelectionSet
                                    (rightField :: rightRest) } := by
                                simpa [hlookup, hcomposite] using hmatch.symm
                              subst task
                              have hrightNameNotMem :
                                  rightName ∉ rest.map Prod.fst := by
                                intro hmember
                                apply hnodupParts.1
                                simpa [beq_iff_eq.mp hname] using hmember
                              have hrestFalse :=
                                executableGroupIncludedBool_eq_false_of_name_not_mem
                                  schema
                                  (fun outputType => childIncludes
                                    (schema.getPossibleTypes outputType.namedType))
                                  rest (rightName, rightField :: rightRest)
                                  hrightNameNotMem
                              unfold executableGroupIncludedBool at hrestFalse
                              rw [hrestFalse, Bool.or_false] at hinclude
                              simpa [hlookup, hcomposite] using hinclude

theorem matchInclusionChildTask?_exists_of_include
    (schema : Schema)
    (childIncludes : List Name -> List Selection -> List Selection -> Bool)
    (rightGroup : Name × List ExecutableField)
    (leftGroups : List (Name × List ExecutableField))
    (hnodup : (leftGroups.map Prod.fst).Nodup)
    (hinclude
      : executableGroupIncludedBool schema
          (fun outputType => childIncludes (schema.getPossibleTypes outputType.namedType))
          leftGroups rightGroup
        = true)
    : ∃ task, matchInclusionChildTask? schema rightGroup leftGroups = some task := by
  unfold executableGroupIncludedBool at hinclude
  rw [List.any_eq_true] at hinclude
  rcases hinclude with ⟨witness, hwitness, hincluded⟩
  rcases witness with ⟨witnessName, witnessFields⟩
  rcases rightGroup with ⟨rightName, rightFields⟩
  have hincludedParts := hincluded
  simp only [Bool.and_eq_true] at hincludedParts
  have hwitnessName : witnessName = rightName := beq_iff_eq.mp hincludedParts.1
  cases witnessFields with
  | nil => simp at hincludedParts
  | cons witnessField witnessRest =>
      cases rightFields with
      | nil => simp at hincludedParts
      | cons rightField rightRest =>
          have hcompatible :
              (witnessField.parentType == rightField.parentType
                && witnessField.fieldName == rightField.fieldName
                && Argument.argumentsSyntacticallyEquivalentBool witnessField.arguments
                  rightField.arguments) = true := by
            have hcompatibleAnd := hincludedParts.2
            rw [Bool.and_eq_true] at hcompatibleAnd
            exact hcompatibleAnd.1
          cases hlookup
                : schema.lookupField rightField.parentType rightField.fieldName with
          | none => simp [hlookup] at hincludedParts
          | some definition =>
              induction leftGroups with
              | nil => simp at hwitness
              | cons candidate rest ih =>
                  have hnodupParts := List.nodup_cons.mp hnodup
                  rcases List.mem_cons.mp hwitness with heq | hwitness
                  · subst candidate
                    cases hcomposite : definition.outputType.isCompositeBool schema with
                    | false =>
                        exact ⟨.leaf, by
                          simp [matchInclusionChildTask?, hwitnessName, hcompatible,
                            hlookup, hcomposite]⟩
                    | true =>
                        exact ⟨.composite {
                            possibleTypes := schema.getPossibleTypes
                              definition.outputType.namedType
                            leftSelectionSet := executableFieldsMergedSelectionSet
                              (witnessField :: witnessRest)
                            rightSelectionSet := executableFieldsMergedSelectionSet
                              (rightField :: rightRest) }, by
                          simp [matchInclusionChildTask?, hwitnessName, hcompatible,
                            hlookup, hcomposite]⟩
                  · have hcandidateName : candidate.1 ≠ rightName := by
                      intro heq
                      apply hnodupParts.1
                      exact List.mem_map.mpr
                        ⟨(witnessName, witnessField :: witnessRest), hwitness,
                          hwitnessName.trans heq.symm⟩
                    rcases ih hnodupParts.2 hwitness with ⟨task, htask⟩
                    exact ⟨task, by
                      simp [matchInclusionChildTask?, beq_iff_eq, hcandidateName,
                        htask]⟩

theorem inclusionChildTasks?_exists_of_include
    (schema : Schema)
    (childIncludes : List Name -> List Selection -> List Selection -> Bool)
    (leftGroups rightGroups : List (Name × List ExecutableField))
    (hnodup : (leftGroups.map Prod.fst).Nodup)
    (hinclude
      : executableGroupsIncludeBool schema
          (fun outputType => childIncludes (schema.getPossibleTypes outputType.namedType))
          leftGroups rightGroups
        = true)
    : ∃ tasks, inclusionChildTasks? schema leftGroups rightGroups = some tasks := by
  induction rightGroups with
  | nil => exact ⟨[], by simp [inclusionChildTasks?]⟩
  | cons rightGroup rest ih =>
      have hparts : executableGroupIncludedBool schema
              (fun outputType => childIncludes
                (schema.getPossibleTypes outputType.namedType))
              leftGroups rightGroup = true
          ∧ executableGroupsIncludeBool schema
              (fun outputType => childIncludes
                (schema.getPossibleTypes outputType.namedType))
              leftGroups rest = true := by
        simpa [executableGroupsIncludeBool, Bool.and_eq_true] using hinclude
      rcases matchInclusionChildTask?_exists_of_include schema childIncludes
          rightGroup leftGroups hnodup hparts.1 with ⟨task, htask⟩
      rcases ih hparts.2 with ⟨tasks, htasks⟩
      cases task with
      | leaf =>
          exact ⟨tasks, by simp [inclusionChildTasks?, htask, htasks]⟩
      | composite childTask =>
          exact ⟨childTask :: tasks, by
            simp [inclusionChildTasks?, htask, htasks]⟩

theorem inclusionChildTasks?_children_true
    (schema : Schema)
    (childIncludes : List Name -> List Selection -> List Selection -> Bool)
    (leftGroups rightGroups : List (Name × List ExecutableField))
    (tasks : List InclusionChildTask)
    (hnodup : (leftGroups.map Prod.fst).Nodup)
    (hmatch : inclusionChildTasks? schema leftGroups rightGroups = some tasks)
    (hinclude
      : executableGroupsIncludeBool schema
          (fun outputType => childIncludes (schema.getPossibleTypes outputType.namedType))
          leftGroups rightGroups
        = true)
    : tasks.all
        fun task =>
          childIncludes task.possibleTypes task.leftSelectionSet
            task.rightSelectionSet := by
  induction rightGroups generalizing tasks with
  | nil =>
      simp [inclusionChildTasks?] at hmatch
      subst tasks
      simp
  | cons rightGroup rest ih =>
      have hparts : executableGroupIncludedBool schema
              (fun outputType => childIncludes
                (schema.getPossibleTypes outputType.namedType))
              leftGroups rightGroup = true
          ∧ executableGroupsIncludeBool schema
              (fun outputType => childIncludes
                (schema.getPossibleTypes outputType.namedType))
              leftGroups rest = true := by
        simpa [executableGroupsIncludeBool, Bool.and_eq_true] using hinclude
      simp only [inclusionChildTasks?] at hmatch
      cases hhead : matchInclusionChildTask? schema rightGroup leftGroups with
      | none => simp [hhead] at hmatch
      | some headTask =>
          cases htail : inclusionChildTasks? schema leftGroups rest with
          | none => simp [hhead, htail] at hmatch
          | some tailTasks =>
              cases headTask with
              | leaf =>
                  simp [hhead, htail, Option.bind_eq_bind] at hmatch
                  subst tasks
                  exact ih tailTasks htail hparts.2
              | composite headTask =>
                  simp [hhead, htail, Option.bind_eq_bind] at hmatch
                  subst tasks
                  rw [List.all_cons, Bool.and_eq_true]
                  exact ⟨matchInclusionChildTask?_child_true schema childIncludes
                    rightGroup leftGroups headTask hnodup hhead hparts.1,
                    ih tailTasks htail hparts.2⟩

theorem inclusionChildTasks?_sound (schema : Schema)
    (childIncludes : List Name -> List Selection -> List Selection -> Bool)
    (leftGroups rightGroups : List (Name × List ExecutableField))
    (tasks : List InclusionChildTask)
    (hmatch : inclusionChildTasks? schema leftGroups rightGroups = some tasks)
    (htasks
      : tasks.all
          fun task =>
            childIncludes task.possibleTypes task.leftSelectionSet task.rightSelectionSet)
    : executableGroupsIncludeBool schema
        (fun outputType => childIncludes (schema.getPossibleTypes outputType.namedType))
        leftGroups rightGroups
      = true := by
  unfold executableGroupsIncludeBool executableGroupIncludedBool
  induction rightGroups generalizing tasks with
  | nil => simp
  | cons rightGroup rest ih =>
      simp only [inclusionChildTasks?] at hmatch
      cases hhead : matchInclusionChildTask? schema rightGroup leftGroups with
      | none => simp [hhead] at hmatch
      | some task =>
          cases htail : inclusionChildTasks? schema leftGroups rest with
          | none => simp [hhead, htail] at hmatch
          | some tailTasks =>
              simp only [hhead, htail, Option.bind_eq_bind] at hmatch
              cases task with
              | leaf =>
                  simp only [Option.bind_some, Option.pure_def,
                    Option.some.injEq] at hmatch
                  subst tasks
                  simp only [List.all_cons]
                  rw [Bool.and_eq_true]
                  constructor
                  · exact matchInclusionChildTask?_sound schema childIncludes
                      rightGroup leftGroups .leaf hhead (by simp)
                  · exact ih tailTasks htail htasks
              | composite headTask =>
                  simp only [Option.bind_some, Option.pure_def,
                    Option.some.injEq] at hmatch
                  subst tasks
                  simp only [List.all_cons] at htasks ⊢
                  have htasks :
                      childIncludes headTask.possibleTypes headTask.leftSelectionSet
                            headTask.rightSelectionSet = true
                        ∧ (tailTasks.all fun task =>
                            childIncludes task.possibleTypes task.leftSelectionSet
                              task.rightSelectionSet) = true := by
                    simpa only [Bool.and_eq_true] using htasks
                  rw [Bool.and_eq_true]
                  constructor
                  · exact matchInclusionChildTask?_sound schema childIncludes
                      rightGroup leftGroups (.composite headTask) hhead
                      (by
                        intro childTask heq
                        injection heq with heq
                        subst childTask
                        exact htasks.1)
                  · exact ih tailTasks htail htasks.2

theorem inclusionChildTaskEqBool_iff (left right : InclusionChildTask)
    : inclusionChildTaskEqBool left right = true ↔ left = right := by
  constructor
  · intro h
    simp only [inclusionChildTaskEqBool, Bool.and_eq_true] at h
    have hpossible : left.possibleTypes = right.possibleTypes :=
      beq_iff_eq.mp h.1.1
    have hleft : left.leftSelectionSet = right.leftSelectionSet :=
      Algorithms.selectionSetEqBool_eq h.1.2
    have hright : left.rightSelectionSet = right.rightSelectionSet :=
      Algorithms.selectionSetEqBool_eq h.2
    cases left
    cases right
    simp_all
  · intro h
    subst right
    simp [inclusionChildTaskEqBool,
      Algorithms.selectionSetEqBool_self]

theorem mem_insertInclusionChildTask
    (source task : InclusionChildTask) (tasks : List InclusionChildTask)
    : source ∈ insertInclusionChildTask task tasks ↔ source = task ∨ source ∈ tasks := by
  induction tasks with
  | nil => simp [insertInclusionChildTask]
  | cons candidate rest ih =>
      simp only [insertInclusionChildTask]
      cases heq : inclusionChildTaskEqBool task candidate
      · simp [ih]
        constructor
        · intro h
          rcases h with hcandidate | htask | hrest
          · exact Or.inr (Or.inl hcandidate)
          · exact Or.inl htask
          · exact Or.inr (Or.inr hrest)
        · intro h
          rcases h with htask | hcandidate | hrest
          · exact Or.inr (Or.inl htask)
          · exact Or.inl hcandidate
          · exact Or.inr (Or.inr hrest)
      · have htask : task = candidate :=
          (inclusionChildTaskEqBool_iff task candidate).mp heq
        subst candidate
        simp

theorem mem_deduplicateInclusionChildTasks
    (source : InclusionChildTask) (tasks : List InclusionChildTask)
    : source ∈ deduplicateInclusionChildTasks tasks ↔ source ∈ tasks := by
  induction tasks with
  | nil => simp [deduplicateInclusionChildTasks]
  | cons task rest ih =>
      rw [deduplicateInclusionChildTasks, mem_insertInclusionChildTask, ih]
      simp

theorem deduplicateInclusionChildTasks_all
    (tasks : List InclusionChildTask) (predicate : InclusionChildTask -> Bool)
    (hall : tasks.all predicate = true)
    : (deduplicateInclusionChildTasks tasks).all predicate = true := by
  apply List.all_eq_true.mpr
  intro task htask
  exact List.all_eq_true.mp hall task
    ((mem_deduplicateInclusionChildTasks task tasks).mp htask)

theorem inclusionChildTasksForParentTypes?_contains
    (schema : Schema)
    (leftGroups rightGroups : List (Name × List ExecutableField))
    {parentTypes : List Name} {merged : List InclusionChildTask}
    (hmatch
      : inclusionChildTasksForParentTypes? schema leftGroups rightGroups parentTypes
        = some merged)
    {parentType : Name} (hparent : parentType ∈ parentTypes)
    : ∃ tasks,
        inclusionChildTasks? schema
            (executableGroupsWithParentType parentType leftGroups)
            (executableGroupsWithParentType parentType rightGroups)
          = some tasks
        ∧ ∀ source, source ∈ tasks -> source ∈ merged := by
  induction parentTypes generalizing merged with
  | nil => simp at hparent
  | cons candidate rest ih =>
      simp only [inclusionChildTasksForParentTypes?] at hmatch
      let candidateLeftGroups :=
        executableGroupsWithParentType candidate leftGroups
      let candidateRightGroups :=
        executableGroupsWithParentType candidate rightGroups
      cases hcandidate
            : inclusionChildTasks? schema candidateLeftGroups candidateRightGroups with
      | none => simp [candidateLeftGroups, candidateRightGroups, hcandidate] at hmatch
      | some candidateTasks =>
          cases hrest
                : inclusionChildTasksForParentTypes? schema leftGroups rightGroups
                    rest with
          | none => simp [candidateLeftGroups, candidateRightGroups, hcandidate,
              hrest] at hmatch
          | some restTasks =>
              simp [candidateLeftGroups, candidateRightGroups, hcandidate, hrest]
                at hmatch
              subst merged
              rcases List.mem_cons.mp hparent with heq | hparent
              · subst parentType
                exact ⟨candidateTasks, hcandidate, by
                  intro source hsource
                  exact (mem_deduplicateInclusionChildTasks source _).mpr
                    (List.mem_append_left _ hsource)⟩
              · rcases ih hrest hparent with ⟨tasks, htasks, hcovered⟩
                refine ⟨tasks, htasks, ?_⟩
                intro source hsource
                exact (mem_deduplicateInclusionChildTasks source _).mpr
                  (List.mem_append_right _ (hcovered source hsource))

theorem inclusionChildTasksForParentTypes?_exists_of_include
    (schema : Schema)
    (childIncludes : List Name -> List Selection -> List Selection -> Bool)
    (leftGroups rightGroups : List (Name × List ExecutableField))
    (parentTypes : List Name)
    (hnodup
      : ∀ parentType,
          parentType ∈ parentTypes
          -> ((executableGroupsWithParentType parentType leftGroups).map Prod.fst).Nodup)
    (hinclude
      : ∀ parentType,
          parentType ∈ parentTypes
          -> executableGroupsIncludeBool schema
                (fun outputType =>
                  childIncludes (schema.getPossibleTypes outputType.namedType))
                (executableGroupsWithParentType parentType leftGroups)
                (executableGroupsWithParentType parentType rightGroups)
              = true)
    : ∃ tasks,
        inclusionChildTasksForParentTypes? schema leftGroups rightGroups parentTypes
          = some tasks
        ∧ tasks.all
            fun task =>
              childIncludes task.possibleTypes task.leftSelectionSet
                task.rightSelectionSet := by
  induction parentTypes with
  | nil => exact ⟨[], by simp [inclusionChildTasksForParentTypes?]⟩
  | cons parentType rest ih =>
      let parentLeftGroups := executableGroupsWithParentType parentType leftGroups
      let parentRightGroups := executableGroupsWithParentType parentType rightGroups
      have hparentInclude := hinclude parentType (by simp)
      rcases inclusionChildTasks?_exists_of_include schema childIncludes
          parentLeftGroups parentRightGroups (hnodup parentType (by simp))
          hparentInclude with
        ⟨parentTasks, hparentTasks⟩
      have hparentChildren := inclusionChildTasks?_children_true schema childIncludes
        parentLeftGroups parentRightGroups parentTasks
        (hnodup parentType (by simp)) hparentTasks hparentInclude
      rcases ih
          (by
            intro candidate hcandidate
            exact hnodup candidate (by simp [hcandidate]))
          (by
            intro candidate hcandidate
            exact hinclude candidate (by simp [hcandidate])) with
        ⟨restTasks, hrestTasks, hrestChildren⟩
      refine ⟨deduplicateInclusionChildTasks (parentTasks ++ restTasks), ?_, ?_⟩
      · simp [inclusionChildTasksForParentTypes?, parentLeftGroups, parentRightGroups,
          hparentTasks, hrestTasks]
      · apply deduplicateInclusionChildTasks_all
        simpa [List.all_append, Bool.and_eq_true] using
          And.intro hparentChildren hrestChildren

theorem group_eq_of_mem_of_mem_of_keysNodup {groups : List (Name × List ExecutableField)}
    {left right : Name × List ExecutableField} (hnodup : (groups.map Prod.fst).Nodup)
    (hleft : left ∈ groups) (hright : right ∈ groups) (hkey : left.1 = right.1)
    : left = right := by
  induction groups generalizing left right with
  | nil => simp at hleft
  | cons head rest ih =>
      simp only [List.map_cons, List.nodup_cons] at hnodup
      rcases List.mem_cons.mp hleft with rfl | hleftRest
      · rcases List.mem_cons.mp hright with rfl | hrightRest
        · rfl
        · exfalso
          exact hnodup.1 (List.mem_map.mpr ⟨right, hrightRest, hkey.symm⟩)
      · rcases List.mem_cons.mp hright with rfl | hrightRest
        · exfalso
          exact hnodup.1 (List.mem_map.mpr ⟨left, hleftRest, hkey⟩)
        · exact ih hnodup.2 hleftRest hrightRest hkey

theorem executableGroupsIncludeBool_child_at_runtime
    (schema : Schema) (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (responseFuel : Nat) (variableValues : VariableValues)
    (leftGroups rightGroups : List (Name × List ExecutableField))
    (leftName rightName : Name) (leftFields rightFields : List ExecutableField)
    (fieldType : TypeRef) (childRuntimeType : Name)
    (hleftNodup : (leftGroups.map Prod.fst).Nodup)
    (hleftReady : executableGroupsSemanticsReady schema leftGroups)
    (hrightReady : executableGroupsSemanticsReady schema rightGroups)
    (hleftGroup : (leftName, leftFields) ∈ leftGroups)
    (hrightGroup : (rightName, rightFields) ∈ rightGroups)
    (hname : leftName = rightName)
    (hleftWitness : completionFieldsWitness schema fieldType leftFields)
    (hrightWitness : completionFieldsWitness schema fieldType rightFields)
    (hchildRuntime : childRuntimeType ∈ schema.getPossibleTypes fieldType.namedType)
    (hinclude
      : executableGroupsIncludeBool schema
          (fun outputType leftSelectionSet rightSelectionSet =>
            (schema.getPossibleTypes outputType.namedType).all
              fun candidateRuntimeType =>
                selectionSetIncludesBoolWithFuel schema responseFuel candidateRuntimeType
                  variableValues leftSelectionSet rightSelectionSet)
          leftGroups rightGroups
        = true)
    : selectionSetIncludesAtRuntimeBoolWithFuel schema responseFuel childRuntimeType
        childRuntimeType variableValues
        (executableFieldsMergedSelectionSet leftFields)
        (executableFieldsMergedSelectionSet rightFields)
      = true := by
  have hrightIncluded := List.all_eq_true.mp hinclude
    (rightName, rightFields) hrightGroup
  unfold executableGroupIncludedBool at hrightIncluded
  rcases List.any_eq_true.mp hrightIncluded with
    ⟨candidate, hcandidate, hcandidateCheck⟩
  rcases candidate with ⟨candidateName, candidateFields⟩
  simp only [Bool.and_eq_true] at hcandidateCheck
  have hcandidateName : candidateName = rightName :=
    beq_iff_eq.mp hcandidateCheck.1
  have hcandidateEq : (candidateName, candidateFields) = (leftName, leftFields) :=
    group_eq_of_mem_of_mem_of_keysNodup hleftNodup hcandidate hleftGroup
      (by simp [hcandidateName, hname])
  injection hcandidateEq with hcandidateNameEq hcandidateFieldsEq
  subst candidateName
  subst candidateFields
  have hleftFieldsReady := hleftReady leftName leftFields hleftGroup
  have hrightFieldsReady := hrightReady rightName rightFields hrightGroup
  cases hleftFields : leftFields with
  | nil => exact False.elim (hleftFieldsReady.1 hleftFields)
  | cons leftHead leftRest =>
      cases hrightFields : rightFields with
      | nil => exact False.elim (hrightFieldsReady.1 hrightFields)
      | cons rightHead rightRest =>
          subst leftFields
          subst rightFields
          simp only [Bool.and_eq_true] at hcandidateCheck
          have hlookupName := hcandidateCheck.2.1
          have hchildCheck := hcandidateCheck.2.2
          rcases hrightWitness with
            ⟨rightSource, rightDefinition, hrightSource, hrightSourceLookup,
              hrightType⟩
          rcases hrightFieldsReady.2.2.1 rightSource rightHead hrightSource
              (by simp) with
            ⟨hrightParent, hrightField, _hrightArguments⟩
          have hrightHeadLookup : schema.lookupField rightHead.parentType
              rightHead.fieldName = some rightDefinition := by
            simpa [hrightParent, hrightField] using hrightSourceLookup
          have hcomposite : rightDefinition.outputType.isCompositeBool schema = true := by
            have hincludes : schema.typeIncludesObjectBool
                rightDefinition.outputType.namedType childRuntimeType = true := by
              rw [← hrightType]
              exact List.contains_iff_mem.mpr hchildRuntime
            change (TypeRef.named rightDefinition.outputType.namedType).isCompositeBool
              schema = true
            unfold Schema.typeIncludesObjectBool Schema.getPossibleTypes at hincludes
            unfold TypeRef.isCompositeBool TypeRef.namedType
            cases hlookup : schema.lookupType rightDefinition.outputType.namedType with
            | none => simp [hlookup] at hincludes
            | some typeDefinition =>
                cases typeDefinition <;> simp [hlookup] at hincludes ⊢
          simp only [hrightHeadLookup, hcomposite, if_true] at hchildCheck
          have hchildSelectionCheck := List.all_eq_true.mp hchildCheck
            childRuntimeType (by
              rw [← hrightType]
              exact hchildRuntime)
          have hchildObject : schema.objectType childRuntimeType :=
            SchemaWellFormedness.schemaWellFormed_possibleTypesAreObjects hschema
              fieldType.namedType childRuntimeType hchildRuntime
          rw [selectionSetIncludesBoolWithFuel.eq_def, List.all_eq_true] at hchildSelectionCheck
          exact hchildSelectionCheck childRuntimeType (by
            have hself :=
              NormalForm.object_typeIncludesObjectBool_self schema hchildObject
            simpa [Schema.typeIncludesObjectBool] using List.contains_iff_mem.mp hself)

theorem mem_splitPossibleTypeRegion
    {region allowed : List Name} {runtimeType : Name}
    (hruntime : runtimeType ∈ region)
    : ∃ subregion,
        subregion ∈ splitPossibleTypeRegion region allowed ∧ runtimeType ∈ subregion := by
  by_cases hallowed : runtimeType ∈ allowed
  · let included := region.filter allowed.contains
    have hruntimeIncluded : runtimeType ∈ included := by
      exact List.mem_filter.mpr
        ⟨hruntime, List.contains_iff_mem.mpr hallowed⟩
    refine ⟨included, ?_, ?_⟩
    · unfold splitPossibleTypeRegion
      have hnonempty : included.isEmpty = false := by
        exact List.isEmpty_eq_false_iff.mpr (by
          intro hempty
          rw [hempty] at hruntimeIncluded
          simp at hruntimeIncluded)
      simp only [included, hnonempty]
      exact List.mem_append.mpr (Or.inl (by simp))
    · exact hruntimeIncluded
  · let excluded := region.filter fun typeName => !allowed.contains typeName
    have hruntimeExcluded : runtimeType ∈ excluded := by
      exact List.mem_filter.mpr
        ⟨hruntime, by simpa using hallowed⟩
    refine ⟨excluded, ?_, ?_⟩
    · unfold splitPossibleTypeRegion
      have hnonempty : excluded.isEmpty = false := by
        exact List.isEmpty_eq_false_iff.mpr (by
          intro hempty
          rw [hempty] at hruntimeExcluded
          simp at hruntimeExcluded)
      simp only [excluded, hnonempty]
      exact List.mem_append.mpr (Or.inr (by simp))
    · exact hruntimeExcluded

theorem boolVarsComplete_mono {variables available : List Name}
    {variableValues : VariableValues}
    (hcomplete : boolVarsComplete available variableValues)
    (hsubset : ∀ variableName, variableName ∈ variables -> variableName ∈ available)
    : boolVarsComplete variables variableValues := by
  intro variableName hvariable
  exact hcomplete variableName (hsubset variableName hvariable)

def KnownBooleanVariablesWithin (knownValues : VariableValues) (available : List Name)
    : Prop :=
  ∀ variableName value,
    inputValueBoolean? knownValues (.variable variableName) = some value
    -> variableName ∈ available

theorem knownBooleanVariablesWithin_nil (available : List Name)
    : KnownBooleanVariablesWithin [] available := by
  intro variableName value hvalue
  simp [inputValueBoolean?, lookupVariableValue?] at hvalue

theorem knownBooleanVariablesWithin_cons
    {knownValues : VariableValues} {available : List Name}
    {variableName : Name} {value : Bool}
    (hknown : KnownBooleanVariablesWithin knownValues available)
    (hvariable : variableName ∈ available)
    : KnownBooleanVariablesWithin
        ((variableName, .boolean value) :: knownValues) available := by
  intro candidate candidateValue hcandidate
  by_cases heq : variableName = candidate
  · simpa [heq] using hvariable
  · simp [inputValueBoolean?, lookupVariableValue?, heq] at hcandidate
    exact hknown candidate candidateValue hcandidate

theorem inputValueBoolean?_representativeBooleanValues_eq_some
    (variables : List Name) (variableValues : VariableValues)
    {variableName : Name} {value : Bool}
    (hvariable : variableName ∈ variables)
    (hvalue : inputValueBoolean? variableValues (.variable variableName) = some value)
    : inputValueBoolean? (representativeBooleanValues variables variableValues)
        (.variable variableName)
      = some value := by
  induction variables with
  | nil => simp at hvariable
  | cons head rest ih =>
      by_cases heq : head = variableName
      · subst head
        simp only [representativeBooleanValues]
        rw [hvalue]
        simp [inputValueBoolean?, lookupVariableValue?, InputValue.staticBoolean?,
          ConstInputValue.toInputValue]
      · have hrest : variableName ∈ rest := by
          rcases List.mem_cons.mp hvariable with hhead | hrest
          · exact False.elim (heq hhead.symm)
          · exact hrest
        simpa only [representativeBooleanValues, inputValueBoolean?,
          lookupVariableValue?, if_neg heq] using ih hrest

theorem representativeBooleanValues_agree
    {available : List Name} {knownValues : VariableValues}
    (hknown : KnownBooleanVariablesWithin knownValues available)
    : BooleanAssignmentsAgree knownValues
        (representativeBooleanValues available knownValues) := by
  intro variableName value hvalue
  exact inputValueBoolean?_representativeBooleanValues_eq_some available knownValues
    (hknown variableName value hvalue) hvalue

theorem getPossibleTypes_eq_singleton_of_object
    (schema : Schema) {typeName : Name} (hobject : schema.objectType typeName)
    : schema.getPossibleTypes typeName = [typeName] := by
  rcases hobject with ⟨objectType, hlookup⟩
  have hname : objectType.name = typeName := by
    have hmatch := List.find?_some hlookup
    simpa [Schema.lookupType, TypeDefinition.name] using hmatch
  simp [Schema.getPossibleTypes, hlookup, hname]

theorem refinePossibleTypeRegions_cover
    {regions : List (List Name)} {condition : SelectionConditions.Condition}
    {runtimeType : Name}
    (hcovered : ∃ region, region ∈ regions ∧ runtimeType ∈ region)
    : ∃ region,
        region ∈ refinePossibleTypeRegions regions condition ∧ runtimeType ∈ region := by
  rcases hcovered with ⟨region, hregion, hruntime⟩
  rcases mem_splitPossibleTypeRegion (allowed := condition.possibleTypes) hruntime with
    ⟨refined, hrefined, hruntimeRefined⟩
  exact ⟨refined, List.mem_flatMap.mpr ⟨region, hregion, hrefined⟩,
    hruntimeRefined⟩

def RegionUniformForPossibleTypes (region possibleTypes : List Name) : Prop :=
  ∀ left,
    left ∈ region
    -> ∀ right,
        right ∈ region -> possibleTypes.contains left = possibleTypes.contains right

def RegionsUniformForPossibleTypes
    (regions : List (List Name)) (possibleTypes : List Name)
    : Prop :=
  ∀ region, region ∈ regions -> RegionUniformForPossibleTypes region possibleTypes

theorem mem_of_mem_splitPossibleTypeRegion
    {region allowed subregion : List Name}
    (hsubregion : subregion ∈ splitPossibleTypeRegion region allowed)
    {runtimeType : Name} (hruntime : runtimeType ∈ subregion)
    : runtimeType ∈ region := by
  unfold splitPossibleTypeRegion at hsubregion
  rcases List.mem_append.mp hsubregion with hincluded | hexcluded
  · split at hincluded
    · simp at hincluded
    · simp only [List.mem_singleton] at hincluded
      subst subregion
      exact (List.mem_filter.mp hruntime).1
  · split at hexcluded
    · simp at hexcluded
    · simp only [List.mem_singleton] at hexcluded
      subst subregion
      exact (List.mem_filter.mp hruntime).1

theorem splitPossibleTypeRegion_uniform
    (region allowed subregion : List Name)
    (hsubregion : subregion ∈ splitPossibleTypeRegion region allowed)
    : RegionUniformForPossibleTypes subregion allowed := by
  intro left hleft right hright
  unfold splitPossibleTypeRegion at hsubregion
  rcases List.mem_append.mp hsubregion with hincluded | hexcluded
  · split at hincluded
    · simp at hincluded
    · simp only [List.mem_singleton] at hincluded
      subst subregion
      exact (List.mem_filter.mp hleft).2.trans (List.mem_filter.mp hright).2.symm
  · split at hexcluded
    · simp at hexcluded
    · simp only [List.mem_singleton] at hexcluded
      subst subregion
      have hleftExcluded := (List.mem_filter.mp hleft).2
      have hrightExcluded := (List.mem_filter.mp hright).2
      simpa using hleftExcluded.trans hrightExcluded.symm

theorem refinePossibleTypeRegions_uniform
    (regions : List (List Name)) (condition : SelectionConditions.Condition)
    : RegionsUniformForPossibleTypes
        (refinePossibleTypeRegions regions condition) condition.possibleTypes := by
  intro subregion hsubregion
  rcases List.mem_flatMap.mp hsubregion with ⟨region, _hregion, hrefined⟩
  exact splitPossibleTypeRegion_uniform region condition.possibleTypes subregion
    hrefined

theorem refinePossibleTypeRegions_preserves_uniform
    {regions : List (List Name)} {possibleTypes : List Name}
    (huniform : RegionsUniformForPossibleTypes regions possibleTypes)
    (condition : SelectionConditions.Condition)
    : RegionsUniformForPossibleTypes
        (refinePossibleTypeRegions regions condition) possibleTypes := by
  intro subregion hsubregion
  rcases List.mem_flatMap.mp hsubregion with ⟨region, hregion, hrefined⟩
  have hsourceUniform := huniform region hregion
  intro left hleft right hright
  exact hsourceUniform left (mem_of_mem_splitPossibleTypeRegion hrefined hleft)
    right (mem_of_mem_splitPossibleTypeRegion hrefined hright)

theorem foldRefinePossibleTypeRegions_preserves_uniform
    (conditions : List SelectionConditions.Condition) (regions : List (List Name))
    (possibleTypes : List Name)
    (huniform : RegionsUniformForPossibleTypes regions possibleTypes)
    : RegionsUniformForPossibleTypes
        (conditions.foldl refinePossibleTypeRegions regions) possibleTypes := by
  induction conditions generalizing regions with
  | nil => exact huniform
  | cons condition rest ih =>
      simp only [List.foldl_cons]
      exact ih (refinePossibleTypeRegions regions condition)
        (refinePossibleTypeRegions_preserves_uniform huniform condition)

theorem foldRefinePossibleTypeRegions_uniform_of_mem
    (conditions : List SelectionConditions.Condition) (regions : List (List Name))
    {condition : SelectionConditions.Condition} (hcondition : condition ∈ conditions)
    : RegionsUniformForPossibleTypes
        (conditions.foldl refinePossibleTypeRegions regions)
        condition.possibleTypes := by
  induction conditions generalizing regions with
  | nil => simp at hcondition
  | cons head rest ih =>
      simp only [List.foldl_cons]
      rcases List.mem_cons.mp hcondition with heq | hrest
      · rw [heq]
        exact foldRefinePossibleTypeRegions_preserves_uniform rest
          (refinePossibleTypeRegions regions head) head.possibleTypes
          (refinePossibleTypeRegions_uniform regions head)
      · exact ih (refinePossibleTypeRegions regions head) hrest

theorem foldRefinePossibleTypeRegions_cover
    (conditions : List SelectionConditions.Condition) (regions : List (List Name))
    {runtimeType : Name}
    (hcovered : ∃ region, region ∈ regions ∧ runtimeType ∈ region)
    : ∃ region,
        region ∈ conditions.foldl refinePossibleTypeRegions regions
        ∧ runtimeType ∈ region := by
  induction conditions generalizing regions with
  | nil => exact hcovered
  | cons condition rest ih =>
      simp only [List.foldl_cons]
      exact ih (refinePossibleTypeRegions regions condition)
        (refinePossibleTypeRegions_cover hcovered)

theorem splitPossibleTypeRegion_subset
    {region allowed subregion : List Name}
    (hsubregion : subregion ∈ splitPossibleTypeRegion region allowed)
    {runtimeType : Name} (hruntime : runtimeType ∈ subregion)
    : runtimeType ∈ region := by
  unfold splitPossibleTypeRegion at hsubregion
  rcases List.mem_append.mp hsubregion with hincluded | hexcluded
  · split at hincluded
    · simp at hincluded
    · simp only [List.mem_singleton] at hincluded
      subst subregion
      exact (List.mem_filter.mp hruntime).1
  · split at hexcluded
    · simp at hexcluded
    · simp only [List.mem_singleton] at hexcluded
      subst subregion
      exact (List.mem_filter.mp hruntime).1

theorem refinePossibleTypeRegions_subset
    {regions : List (List Name)} {condition : SelectionConditions.Condition}
    {subregion : List Name}
    (hsubregion : subregion ∈ refinePossibleTypeRegions regions condition)
    {runtimeType : Name} (hruntime : runtimeType ∈ subregion)
    : ∃ region, region ∈ regions ∧ runtimeType ∈ region := by
  rcases List.mem_flatMap.mp hsubregion with ⟨region, hregion, hrefined⟩
  exact ⟨region, hregion, splitPossibleTypeRegion_subset hrefined hruntime⟩

theorem foldRefinePossibleTypeRegions_subset
    (conditions : List SelectionConditions.Condition) (regions : List (List Name))
    {subregion : List Name}
    (hsubregion : subregion ∈ conditions.foldl refinePossibleTypeRegions regions)
    {runtimeType : Name} (hruntime : runtimeType ∈ subregion)
    : ∃ region, region ∈ regions ∧ runtimeType ∈ region := by
  induction conditions generalizing regions subregion with
  | nil => exact ⟨subregion, hsubregion, hruntime⟩
  | cons condition rest ih =>
      simp only [List.foldl_cons] at hsubregion
      rcases ih (refinePossibleTypeRegions regions condition) hsubregion hruntime with
        ⟨intermediate, hintermediate, hruntime⟩
      exact refinePossibleTypeRegions_subset hintermediate hruntime

end QueryInclusion
end GraphQL
