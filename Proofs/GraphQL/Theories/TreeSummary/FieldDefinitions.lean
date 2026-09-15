import Proofs.GraphQL.Theories.ConditionTree.Soundness
import Proofs.GraphQL.Theories.NormalForm.Shared.SemanticReadiness.Readiness
import GraphQL.Theories.TreeSummary.Core

/-! Validated field-definition compatibility retained by tree-summary extraction. -/

namespace GraphQL
namespace TreeSummary

open GraphQL.ConditionTree
open GraphQL.SelectionConditions

/-- A conditioned source field has a common validated output type for every possible
runtime parent retained by its condition. -/
def FieldEntryDefinitionsCompatible (schema : Schema) (entry : Condition × Selection)
    : Prop :=
  match entry.2 with
  | .field _responseName fieldName _arguments _directives _selectionSet =>
      ∃ expectedOutputType,
        ∀ parentType,
          parentType ∈ entry.1.possibleTypes
          -> ∃ implementation,
              schema.lookupField parentType fieldName = some implementation
              ∧ schema.outputTypeSubtype implementation.outputType expectedOutputType
  | .inlineFragment _typeCondition _directives _selectionSet => True

/-- The validation witness behind one conditioned source field. Besides its compatible
runtime definitions, it retains validity of the child selection set under the source
definition. This is proof-only provenance; executable condition-tree fields remain
unchanged. -/
def FieldEntryValid (schema : Schema)
    (variableDefinitions : List VariableDefinition)
    (entry : Condition × Selection)
    : Prop :=
  match entry.2 with
  | .field _responseName fieldName _arguments _directives selectionSet =>
      ∃ expectedDefinition,
        (∀ parentType,
          parentType ∈ entry.1.possibleTypes
          -> ∃ implementation,
              schema.lookupField parentType fieldName = some implementation
              ∧ schema.outputTypeSubtype implementation.outputType
                  expectedDefinition.outputType)
        ∧ Validation.fieldSelectionSetValid schema variableDefinitions
            expectedDefinition selectionSet
  | .inlineFragment _typeCondition _directives _selectionSet => True

/-- Every stored field in a condition tree retains its source validation witness. -/
def TreeFieldsValid (schema : Schema)
    (variableDefinitions : List VariableDefinition)
    (tree : ConditionTree.Tree)
    : Prop :=
  ∀ entry, entry ∈ tree.fieldEntries -> FieldEntryValid schema variableDefinitions entry

/-- Every occurrence in a collected group retains its source validation witness. -/
def CollectedFieldGroup.FieldsValid (schema : Schema)
    (variableDefinitions : List VariableDefinition)
    (group : CollectedFieldGroup)
    : Prop :=
  ∀ selection,
    selection ∈ group.selections
    -> FieldEntryValid schema variableDefinitions (group.condition, selection)

theorem FieldEntryValid.definitionsCompatible
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {entry : Condition × Selection}
    (hvalid : FieldEntryValid schema variableDefinitions entry)
    : FieldEntryDefinitionsCompatible schema entry := by
  cases entry with
  | mk condition selection =>
      cases selection with
      | field responseName fieldName arguments directives selectionSet =>
          rcases hvalid with ⟨expectedDefinition, hdefinitions, _hchildren⟩
          exact ⟨expectedDefinition.outputType, hdefinitions⟩
      | inlineFragment typeCondition directives selectionSet => trivial

/-- Every stored field in a condition tree has validated runtime definitions. -/
def TreeDefinitionsCompatible (schema : Schema) (tree : ConditionTree.Tree) : Prop :=
  ∀ entry, entry ∈ tree.fieldEntries -> FieldEntryDefinitionsCompatible schema entry

/-- One selected named field is valid throughout the current exact-case region. -/
def NamedFieldDefinitionsCompatible (schema : Schema) (possibleTypes : List Name)
    (field : ConditionTree.NamedField)
    : Prop :=
  ∃ expectedOutputType,
    ∀ parentType,
      parentType ∈ possibleTypes
      -> ∃ implementation,
          schema.lookupField parentType field.field.fieldName = some implementation
          ∧ schema.outputTypeSubtype implementation.outputType expectedOutputType

theorem FieldEntryDefinitionsCompatible.mono
    (schema : Schema) (condition : Condition) (field : ConditionTree.NamedField)
    (possibleTypes : List Name)
    (hentry : FieldEntryDefinitionsCompatible schema (condition, field.toSelection))
    (hsubset
      : ∀ parentType, parentType ∈ possibleTypes -> parentType ∈ condition.possibleTypes)
    : NamedFieldDefinitionsCompatible schema possibleTypes field := by
  rcases hentry with ⟨expectedOutputType, hdefinitions⟩
  exact ⟨expectedOutputType, fun parentType hparent =>
    hdefinitions parentType (hsubset parentType hparent)⟩

theorem FieldEntryValid.mono
    (schema : Schema) (variableDefinitions : List VariableDefinition)
    (source target : Condition) (selection : Selection)
    (hvalid : FieldEntryValid schema variableDefinitions (source, selection))
    (hsubset
      : ∀ parentType,
          parentType ∈ target.possibleTypes -> parentType ∈ source.possibleTypes)
    : FieldEntryValid schema variableDefinitions (target, selection) := by
  cases selection with
  | field responseName fieldName arguments directives selectionSet =>
      rcases hvalid with ⟨definition, hdefinitions, hchildren⟩
      exact ⟨definition, fun parentType hparent =>
        hdefinitions parentType (hsubset parentType hparent), hchildren⟩
  | inlineFragment typeCondition directives selectionSet => trivial

private theorem selection_mem_collectFieldGroups
    (fields : List ConditionTree.NamedField) (selection : Selection)
    : selection
        ∈ (ConditionTree.collectFieldGroups fields).flatMap
            ConditionTree.FieldGroup.selections
      ↔ selection ∈ fields.map ConditionTree.NamedField.toSelection := by
  unfold ConditionTree.collectFieldGroups
  have aux : ∀ (rest : List ConditionTree.NamedField)
      (groups : List ConditionTree.FieldGroup),
      selection ∈ (rest.foldl
          (fun groups field => ConditionTree.addFieldToGroups field groups)
          groups).flatMap ConditionTree.FieldGroup.selections
        ↔ selection ∈ rest.map ConditionTree.NamedField.toSelection
          ∨ selection ∈ groups.flatMap ConditionTree.FieldGroup.selections := by
    intro rest groups
    induction rest generalizing groups with
    | nil => simp
    | cons field tail ih =>
        rw [List.foldl_cons, ih]
        rw [ConditionTree.mem_groupedSelections_addField]
        simp [or_assoc, or_left_comm, or_comm]
  simpa using aux fields []

/-- Grouping compatible named fields by response name preserves compatibility of the
representative chosen for each nonempty group. -/
theorem fieldGroupsWithContext_definitionsCompatible
    (schema : Schema) (inherited : List BooleanLiteral) (condition : Condition)
    (fields : List ConditionTree.NamedField)
    (hfields
      : ∀ field,
          field ∈ fields
          -> NamedFieldDefinitionsCompatible schema condition.possibleTypes field)
    : ∀ group,
        group
          ∈ fieldGroupsWithContext inherited condition
              (ConditionTree.collectFieldGroups fields)
        -> group.FieldDefinitionsCompatible schema := by
  intro group hgroup
  unfold fieldGroupsWithContext at hgroup
  rcases List.mem_map.mp hgroup with ⟨sourceGroup, hsourceGroup, rfl⟩
  have hselectionGroup :
      sourceGroup.first.toSelection sourceGroup.responseName
        ∈ (ConditionTree.collectFieldGroups fields).flatMap
          ConditionTree.FieldGroup.selections := by
    apply List.mem_flatMap.mpr
    exact ⟨sourceGroup, hsourceGroup,
      by simp [ConditionTree.FieldGroup.selections,
        ConditionTree.FieldGroup.fields]⟩
  have hsource := selection_mem_collectFieldGroups fields
    (sourceGroup.first.toSelection sourceGroup.responseName) |>.mp hselectionGroup
  rcases List.mem_map.mp hsource with ⟨sourceField, _hsourceField, heq⟩
  rcases hfields sourceField _hsourceField with
    ⟨expectedOutputType, hcompatible⟩
  cases sourceField
  simp only [ConditionTree.NamedField.toSelection,
    ConditionTree.Field.toSelection, Selection.field.injEq] at heq
  rcases heq with ⟨_hresponseName, hfieldName, _harguments, _hdirectives,
    _hselectionSet⟩
  refine ⟨expectedOutputType, ?_⟩
  intro parentType hparentType
  simpa [CollectedFieldGroup.representativeField, hfieldName] using
    hcompatible parentType hparentType

/-- Grouping named fields preserves every occurrence-level validation witness. -/
theorem fieldGroupsWithContext_fieldsValid
    (schema : Schema) (variableDefinitions : List VariableDefinition)
    (inherited : List BooleanLiteral) (condition : Condition)
    (fields : List ConditionTree.NamedField)
    (hfields
      : ∀ field,
          field ∈ fields
          -> FieldEntryValid schema variableDefinitions (condition, field.toSelection))
    : ∀ group,
        group
          ∈ fieldGroupsWithContext inherited condition
              (ConditionTree.collectFieldGroups fields)
        -> group.FieldsValid schema variableDefinitions := by
  intro group hgroup selection hselection
  unfold fieldGroupsWithContext at hgroup
  rcases List.mem_map.mp hgroup with ⟨sourceGroup, hsourceGroup, rfl⟩
  have hselectionGroup :
      selection ∈ (ConditionTree.collectFieldGroups fields).flatMap
        ConditionTree.FieldGroup.selections := by
    exact List.mem_flatMap.mpr ⟨sourceGroup, hsourceGroup, hselection⟩
  have hsource := selection_mem_collectFieldGroups fields selection |>.mp
    hselectionGroup
  rcases List.mem_map.mp hsource with ⟨sourceField, hsourceField, heq⟩
  rw [← heq]
  exact hfields sourceField hsourceField

theorem CollectedFieldGroup.FieldsValid.definitionsCompatible
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {group : CollectedFieldGroup}
    (hvalid : group.FieldsValid schema variableDefinitions)
    : group.FieldDefinitionsCompatible schema := by
  have hrepresentative :
      group.representativeField.toSelection group.responseName ∈ group.selections := by
    simp [CollectedFieldGroup.selections, CollectedFieldGroup.responseName,
      CollectedFieldGroup.representativeField,
      ConditionTree.FieldGroup.selections, ConditionTree.FieldGroup.fields]
  have hentry := (hvalid _ hrepresentative).definitionsCompatible
  simpa [FieldEntryDefinitionsCompatible, ConditionTree.Field.toSelection,
    CollectedFieldGroup.FieldDefinitionsCompatible] using hentry

private theorem conditionForBranch?_possibleTypes_subset
    (schema : Schema) (inherited : List BooleanLiteral)
    (start target : Condition) (branch : BranchCondition)
    (hresult : conditionForBranch? schema inherited start branch = some target)
    : ∀ runtimeType,
        runtimeType ∈ target.possibleTypes -> runtimeType ∈ start.possibleTypes := by
  intro runtimeType hruntime
  cases branch with
  | typeCondition typeName =>
      simp only [conditionForBranch?] at hresult
      split at hresult
      · contradiction
      · simp only [Option.some.injEq] at hresult
        subst target
        exact (List.mem_filter.mp hruntime).1
  | booleanLiteral literal =>
      simp only [conditionForBranch?] at hresult
      cases hcandidate
            : canonicalBooleanCondition (start.booleanCondition ++ [literal]) with
      | none => simp [hcandidate] at hresult
      | some candidate =>
          let filtered := candidate.filter fun item => !inherited.contains item
          rw [hcandidate] at hresult
          change (canonicalBooleanCondition (inherited ++ filtered)).bind
              (fun _ => some { start with booleanCondition := filtered })
            = some target at hresult
          cases hglobal : canonicalBooleanCondition (inherited ++ filtered) with
          | none => simp [hglobal] at hresult
          | some global =>
              rw [hglobal] at hresult
              simp only [Option.bind_some, Option.some.injEq] at hresult
              subst target
              exact hruntime

private theorem conditionForBranches?_possibleTypes_subset
    (schema : Schema) (inherited : List BooleanLiteral)
    (start target : Condition) (branches : List BranchCondition)
    (hresult : conditionForBranches? schema inherited start branches = some target)
    : ∀ runtimeType,
        runtimeType ∈ target.possibleTypes -> runtimeType ∈ start.possibleTypes := by
  induction branches generalizing start with
  | nil =>
      simp [conditionForBranches?] at hresult
      subst target
      exact fun _ h => h
  | cons branch rest ih =>
      rw [conditionForBranches?] at hresult
      cases hnext : conditionForBranch? schema inherited start branch with
      | none => simp [hnext] at hresult
      | some next =>
          rw [hnext] at hresult
          intro runtimeType hruntime
          exact conditionForBranch?_possibleTypes_subset schema inherited start next
            branch hnext runtimeType (ih next hresult runtimeType hruntime)

private theorem parentTypeForBranches_map_booleanLiteral
    (parentType : Name) (literals : List BooleanLiteral)
    : parentTypeForBranches parentType (literals.map BranchCondition.booleanLiteral)
      = parentType := by
  induction literals generalizing parentType with
  | nil => rfl
  | cons literal rest tail_ih =>
      simpa [parentTypeForBranches, BranchCondition.parentType] using
        tail_ih parentType

private theorem parentTypeForInlineBranches_none
    (currentParentType : Name) (directives : List DirectiveApplication)
    (nextBranches : List BranchCondition)
    (hbranches : branchConditionsForInlineFragment? none directives = some nextBranches)
    : parentTypeForBranches currentParentType nextBranches = currentParentType := by
  cases hliterals : literalsForDirectives directives with
  | none => simp [branchConditionsForInlineFragment?, branchConditionsForDirectives?,
      hliterals] at hbranches
  | some literals =>
      simp [branchConditionsForInlineFragment?, branchConditionsForDirectives?,
        hliterals] at hbranches
      subst nextBranches
      exact parentTypeForBranches_map_booleanLiteral currentParentType literals

private theorem parentTypeForInlineBranches_some
    (currentParentType fragmentType : Name)
    (directives : List DirectiveApplication) (nextBranches : List BranchCondition)
    (hbranches
      : branchConditionsForInlineFragment? (some fragmentType) directives
        = some nextBranches)
    : parentTypeForBranches currentParentType nextBranches = fragmentType := by
  cases hliterals : literalsForDirectives directives with
  | none => simp [branchConditionsForInlineFragment?, branchConditionsForDirectives?,
      hliterals] at hbranches
  | some literals =>
      simp [branchConditionsForInlineFragment?, branchConditionsForDirectives?,
        hliterals] at hbranches
      subst nextBranches
      simpa [parentTypeForBranches, BranchCondition.parentType] using
        parentTypeForBranches_map_booleanLiteral fragmentType literals

private theorem inlineBranches_possibleTypes_subset_parent
    (schema : Schema) (currentParentType : Name)
    (inherited : List BooleanLiteral) (currentCondition nextCondition : Condition)
    (typeCondition : Option Name) (directives : List DirectiveApplication)
    (nextBranches : List BranchCondition)
    (hcurrent
      : ∀ runtimeType,
          runtimeType ∈ currentCondition.possibleTypes
          -> runtimeType ∈ schema.getPossibleTypes currentParentType)
    (hbranches
      : branchConditionsForInlineFragment? typeCondition directives = some nextBranches)
    (hnext
      : conditionForBranches? schema inherited currentCondition nextBranches
        = some nextCondition)
    : ∀ runtimeType,
        runtimeType ∈ nextCondition.possibleTypes
        -> runtimeType
            ∈ schema.getPossibleTypes
                (parentTypeForBranches currentParentType nextBranches) := by
  cases hliterals : literalsForDirectives directives with
  | none =>
      simp [branchConditionsForInlineFragment?, branchConditionsForDirectives?,
        hliterals] at hbranches
  | some literals =>
      have hdirectives : branchConditionsForDirectives? directives =
          some (literals.map BranchCondition.booleanLiteral) := by
        simp [branchConditionsForDirectives?, hliterals]
      cases typeCondition with
      | none =>
          simp [branchConditionsForInlineFragment?, hdirectives] at hbranches
          subst nextBranches
          rw [parentTypeForBranches_map_booleanLiteral]
          intro runtimeType hruntime
          exact hcurrent runtimeType
            (conditionForBranches?_possibleTypes_subset schema inherited
              currentCondition nextCondition _ hnext runtimeType hruntime)
      | some fragmentType =>
          have hparent := parentTypeForInlineBranches_some currentParentType
            fragmentType directives nextBranches hbranches
          simp [branchConditionsForInlineFragment?, hdirectives] at hbranches
          subst nextBranches
          rw [hparent]
          rw [conditionForBranches?] at hnext
          cases htype
                : conditionForBranch? schema inherited currentCondition
                    (.typeCondition fragmentType) with
          | none => simp [htype] at hnext
          | some afterType =>
              rw [htype] at hnext
              intro runtimeType hruntime
              have hafter := conditionForBranches?_possibleTypes_subset schema inherited
                afterType nextCondition _ hnext runtimeType hruntime
              simp only [conditionForBranch?] at htype
              split at htype
              · contradiction
              · simp only [Option.some.injEq] at htype
                subst afterType
                exact List.contains_iff_mem.mp (List.mem_filter.mp hafter).2

-- The lookup and child-validity portion of selection validation used by summary
-- extraction. It deliberately omits directive and nonempty-fragment requirements,
-- which known-false pruning need not preserve.
mutual
  def SelectionSourceValid (schema : Schema)
      (variableDefinitions : List VariableDefinition) (parentType : Name)
      : Selection -> Prop
    | .field _responseName fieldName _arguments _directives selectionSet =>
        ∃ definition,
          schema.lookupField parentType fieldName = some definition
          ∧ Validation.fieldSelectionSetValid schema variableDefinitions definition
              selectionSet
    | .inlineFragment none _directives selectionSet =>
        SelectionSetSourceValid schema variableDefinitions parentType selectionSet
    | .inlineFragment (some typeCondition) _directives selectionSet =>
        SelectionSetSourceValid schema variableDefinitions typeCondition selectionSet

  def SelectionSetSourceValid (schema : Schema)
      (variableDefinitions : List VariableDefinition) (parentType : Name)
      (selectionSet : List Selection)
      : Prop :=
    ∀ selection,
      selection ∈ selectionSet
      -> SelectionSourceValid schema variableDefinitions parentType selection
end

theorem SelectionSourceValid.of_selectionValid
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {parentType : Name} {selection : Selection}
    (hvalid : Validation.selectionValid schema variableDefinitions parentType selection)
    : SelectionSourceValid schema variableDefinitions parentType selection := by
  cases selection with
  | field responseName fieldName arguments directives selectionSet =>
      simp only [SelectionSourceValid]
      rcases Validation.selectionValid_field_lookup hvalid with
        ⟨definition, hlookup, _harguments, hchildren⟩
      exact ⟨definition, hlookup, hchildren⟩
  | inlineFragment typeCondition directives selectionSet =>
      cases typeCondition with
      | none =>
          simp only [SelectionSourceValid]
          unfold SelectionSetSourceValid
          intro candidate hcandidate
          have hchildren :=
            Validation.selectionValid_inlineFragment_none_selectionSetValid hvalid
          unfold Validation.selectionSetValid at hchildren
          exact SelectionSourceValid.of_selectionValid
            (hchildren candidate hcandidate)
      | some fragmentType =>
          simp only [SelectionSourceValid]
          unfold SelectionSetSourceValid
          intro candidate hcandidate
          have hchildren :=
            Validation.selectionValid_inlineFragment_some_selectionSetValid hvalid
          unfold Validation.selectionSetValid at hchildren
          exact SelectionSourceValid.of_selectionValid
            (hchildren candidate hcandidate)

theorem SelectionSetSourceValid.of_selectionSetValid
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {parentType : Name} {selectionSet : List Selection}
    (hvalid
      : Validation.selectionSetValid schema variableDefinitions parentType selectionSet)
    : SelectionSetSourceValid schema variableDefinitions parentType selectionSet := by
  unfold SelectionSetSourceValid
  unfold Validation.selectionSetValid at hvalid
  intro selection hselection
  exact SelectionSourceValid.of_selectionValid (hvalid selection hselection)

/-- Each selection may come from a different validated static parent, provided the
current condition's runtime region is contained in that parent's possible objects. -/
def SelectionsValidForCondition (schema : Schema)
    (variableDefinitions : List VariableDefinition) (condition : Condition)
    (selectionSet : List Selection)
    : Prop :=
  ∀ selection,
    selection ∈ selectionSet
    -> ∃ validationParent,
        SelectionSourceValid schema variableDefinitions validationParent selection
        ∧ ∀ runtimeType,
            runtimeType ∈ condition.possibleTypes
            -> runtimeType ∈ schema.getPossibleTypes validationParent

mutual
  theorem collectConditionEntries_fieldsValid
      (schema : Schema) (variableDefinitions : List VariableDefinition)
      (currentParentType : Name)
      (inherited : List BooleanLiteral) (currentCondition : Condition)
      (selectionSet : List Selection)
      (hschema : SchemaWellFormedness.schemaWellFormed schema)
      (hsources
        : SelectionsValidForCondition schema variableDefinitions
            currentCondition selectionSet)
      : ∀ entry,
          entry
            ∈ collectConditionEntries schema currentParentType inherited
                currentCondition selectionSet
          -> FieldEntryValid schema variableDefinitions entry := by
    cases selectionSet with
    | nil => simp [collectConditionEntries]
    | cons selection rest =>
        have hsource := hsources selection (by simp)
        rcases hsource with ⟨validationParent, hselection, hscope⟩
        have hrest : SelectionsValidForCondition schema variableDefinitions
            currentCondition rest := by
          intro candidate hcandidate
          exact hsources candidate (by simp [hcandidate])
        cases selection with
        | field responseName fieldName arguments directives childSelectionSet =>
            simp only [SelectionSourceValid] at hselection
            intro entry hentry
            rw [collectConditionEntries] at hentry
            cases hbranches : branchConditionsForDirectives? directives with
            | none =>
                simp [hbranches] at hentry
                exact collectConditionEntries_fieldsValid schema variableDefinitions
                  currentParentType inherited currentCondition rest hschema hrest
                  entry hentry
            | some nextBranches =>
                cases hnext
                      : conditionForBranches? schema inherited currentCondition
                          nextBranches with
                | none =>
                    simp [hbranches, hnext] at hentry
                    exact collectConditionEntries_fieldsValid schema variableDefinitions
                      currentParentType inherited currentCondition rest hschema hrest
                      entry hentry
                | some nextCondition =>
                    simp only [hbranches, hnext, List.mem_append,
                      List.mem_singleton] at hentry
                    rcases hentry with hentry | hentry
                    · subst entry
                      rcases hselection with
                        ⟨expectedDefinition, hexpected, hchildren⟩
                      refine ⟨expectedDefinition, ?_, hchildren⟩
                      intro runtimeType hruntime
                      have hpossible := hscope runtimeType
                        (conditionForBranches?_possibleTypes_subset schema inherited
                          currentCondition nextCondition nextBranches hnext runtimeType
                          hruntime)
                      rcases
                          SchemaWellFormedness.schemaWellFormed_possibleObject_lookupField_exists
                            hschema hpossible hexpected with
                        ⟨implementation, himplementation⟩
                      exact ⟨implementation, himplementation,
                        SchemaWellFormedness.schemaWellFormed_possibleObject_lookupField_outputTypeSubtype
                          hschema hpossible hexpected himplementation⟩
                    · exact collectConditionEntries_fieldsValid schema variableDefinitions
                        currentParentType inherited currentCondition rest hschema hrest
                        entry hentry
        | inlineFragment typeCondition directives childSelectionSet =>
            intro entry hentry
            rw [collectConditionEntries] at hentry
            cases hbranches
                  : branchConditionsForInlineFragment? typeCondition directives with
            | none =>
                simp [hbranches] at hentry
                exact collectConditionEntries_fieldsValid schema variableDefinitions
                  currentParentType inherited currentCondition rest hschema hrest
                  entry hentry
            | some nextBranches =>
                cases hnext
                      : conditionForBranches? schema inherited currentCondition
                          nextBranches with
                | none =>
                    simp [hbranches, hnext] at hentry
                    exact collectConditionEntries_fieldsValid schema variableDefinitions
                      currentParentType inherited currentCondition rest hschema hrest
                      entry hentry
                | some nextCondition =>
                    simp only [hbranches, hnext, List.mem_append] at hentry
                    rcases hentry with hentry | hentry
                    · have hchildren : SelectionSetSourceValid schema
                          variableDefinitions
                          (parentTypeForBranches validationParent nextBranches)
                          childSelectionSet := by
                        cases typeCondition with
                        | none =>
                            simp only [SelectionSourceValid] at hselection
                            rw [parentTypeForInlineBranches_none validationParent
                              directives nextBranches hbranches]
                            exact hselection
                        | some fragmentType =>
                            simp only [SelectionSourceValid] at hselection
                            rw [parentTypeForInlineBranches_some validationParent
                              fragmentType directives nextBranches hbranches]
                            exact hselection
                      have hchildSources : SelectionsValidForCondition schema
                          variableDefinitions nextCondition childSelectionSet := by
                        intro candidate hcandidate
                        refine ⟨parentTypeForBranches validationParent nextBranches,
                          ?_, ?_⟩
                        · unfold SelectionSetSourceValid at hchildren
                          exact hchildren candidate hcandidate
                        exact inlineBranches_possibleTypes_subset_parent schema
                          validationParent inherited currentCondition nextCondition
                          typeCondition directives nextBranches hscope hbranches hnext
                      exact collectConditionEntries_fieldsValid schema variableDefinitions
                        (parentTypeForBranches currentParentType nextBranches) inherited
                        nextCondition childSelectionSet hschema hchildSources entry hentry
                    · exact collectConditionEntries_fieldsValid schema variableDefinitions
                        currentParentType inherited currentCondition rest hschema hrest
                        entry hentry
  termination_by SelectionSet.size selectionSet
  decreasing_by
    all_goals
      simp_wf
      simp_all [SelectionSet.size, Selection.size]
      omega
end

mutual
  theorem collectConditionEntries_definitionsCompatible
      (schema : Schema) (currentParentType : Name)
      (inherited : List BooleanLiteral) (currentCondition : Condition)
      (selectionSet : List Selection)
      (hschema : SchemaWellFormedness.schemaWellFormed schema)
      (hlookup : NormalForm.selectionSetLookupValid schema currentParentType selectionSet)
      (hcurrent
        : ∀ runtimeType,
            runtimeType ∈ currentCondition.possibleTypes
            -> runtimeType ∈ schema.getPossibleTypes currentParentType)
      : ∀ entry,
          entry
            ∈ collectConditionEntries schema currentParentType inherited
                currentCondition selectionSet
          -> FieldEntryDefinitionsCompatible schema entry := by
    cases selectionSet with
    | nil => simp [collectConditionEntries]
    | cons selection rest =>
        have hhead := NormalForm.selectionSetLookupValid_head hlookup
        have htail := NormalForm.selectionSetLookupValid_tail hlookup
        cases selection with
        | field responseName fieldName arguments directives childSelectionSet =>
            intro entry hentry
            rw [collectConditionEntries] at hentry
            cases hbranches : branchConditionsForDirectives? directives with
            | none =>
                simp [hbranches] at hentry
                exact collectConditionEntries_definitionsCompatible schema
                  currentParentType inherited currentCondition rest hschema htail
                  hcurrent entry hentry
            | some nextBranches =>
                cases hnext
                      : conditionForBranches? schema inherited currentCondition
                          nextBranches with
                | none =>
                    simp [hbranches, hnext] at hentry
                    exact collectConditionEntries_definitionsCompatible schema
                      currentParentType inherited currentCondition rest hschema htail
                      hcurrent entry hentry
                | some nextCondition =>
                    simp only [hbranches, hnext, List.mem_append,
                      List.mem_singleton] at hentry
                    rcases hentry with hentry | hentry
                    · subst entry
                      simp [NormalForm.selectionLookupValid] at hhead
                      rcases hhead with ⟨definition, hdefinition⟩
                      refine ⟨definition.outputType, ?_⟩
                      intro runtimeType hruntime
                      have hpossible := hcurrent runtimeType
                        (conditionForBranches?_possibleTypes_subset schema inherited
                          currentCondition nextCondition nextBranches hnext runtimeType
                          hruntime)
                      rcases
                          SchemaWellFormedness.schemaWellFormed_possibleObject_lookupField_exists
                            hschema hpossible hdefinition with
                        ⟨implementation, himplementation⟩
                      exact ⟨implementation, himplementation,
                        SchemaWellFormedness.schemaWellFormed_possibleObject_lookupField_outputTypeSubtype
                          hschema hpossible hdefinition himplementation⟩
                    · exact collectConditionEntries_definitionsCompatible schema
                        currentParentType inherited currentCondition rest hschema htail
                        hcurrent entry hentry
        | inlineFragment typeCondition directives childSelectionSet =>
            intro entry hentry
            rw [collectConditionEntries] at hentry
            cases hbranches
                  : branchConditionsForInlineFragment? typeCondition directives with
            | none =>
                simp [hbranches] at hentry
                exact collectConditionEntries_definitionsCompatible schema
                  currentParentType inherited currentCondition rest hschema htail
                  hcurrent entry hentry
            | some nextBranches =>
                cases hnext
                      : conditionForBranches? schema inherited currentCondition
                          nextBranches with
                | none =>
                    simp [hbranches, hnext] at hentry
                    exact collectConditionEntries_definitionsCompatible schema
                      currentParentType inherited currentCondition rest hschema htail
                      hcurrent entry hentry
                | some nextCondition =>
                    simp only [hbranches, hnext, List.mem_append] at hentry
                    rcases hentry with hentry | hentry
                    · have hchildLookup : NormalForm.selectionSetLookupValid schema
                          (parentTypeForBranches currentParentType nextBranches)
                          childSelectionSet := by
                        cases typeCondition with
                        | none =>
                            rw [parentTypeForInlineBranches_none currentParentType
                              directives nextBranches hbranches]
                            simpa [NormalForm.selectionLookupValid] using hhead
                        | some fragmentType =>
                            rw [parentTypeForInlineBranches_some currentParentType
                              fragmentType directives nextBranches hbranches]
                            simpa [NormalForm.selectionLookupValid] using hhead
                      exact collectConditionEntries_definitionsCompatible schema
                        (parentTypeForBranches currentParentType nextBranches) inherited
                        nextCondition childSelectionSet hschema hchildLookup
                        (inlineBranches_possibleTypes_subset_parent schema
                          currentParentType inherited currentCondition nextCondition
                          typeCondition directives nextBranches hcurrent hbranches hnext)
                        entry hentry
                    · exact collectConditionEntries_definitionsCompatible schema
                        currentParentType inherited currentCondition rest hschema htail
                        hcurrent entry hentry
  termination_by SelectionSet.size selectionSet
  decreasing_by
    all_goals
      simp_wf
      simp_all [SelectionSet.size, Selection.size]
      omega
end

theorem selectionSetLookupValid_pruneKnownFalseSelections
    (schema : Schema) (variableValues : Execution.VariableValues) (parentType : Name)
    : ∀ selectionSet,
        NormalForm.selectionSetLookupValid schema parentType selectionSet
        -> NormalForm.selectionSetLookupValid schema parentType
            (pruneKnownFalseSelections variableValues selectionSet)
  | [], hlookup => by simpa [pruneKnownFalseSelections] using hlookup
  | selection :: rest, hlookup => by
      have hhead := NormalForm.selectionSetLookupValid_head hlookup
      have htail := NormalForm.selectionSetLookupValid_tail hlookup
      cases selection with
      | field responseName fieldName arguments directives childSelectionSet =>
          unfold ConditionTree.pruneKnownFalseSelections
          split
          · exact selectionSetLookupValid_pruneKnownFalseSelections schema
              variableValues parentType rest htail
          · unfold NormalForm.selectionSetLookupValid
            intro candidate hcandidate
            rcases List.mem_cons.mp hcandidate with rfl | hrest
            · exact hhead
            · have htailPruned :=
                selectionSetLookupValid_pruneKnownFalseSelections schema
                  variableValues parentType rest htail
              unfold NormalForm.selectionSetLookupValid at htailPruned
              exact htailPruned candidate hrest
      | inlineFragment typeCondition directives childSelectionSet =>
          unfold ConditionTree.pruneKnownFalseSelections
          split
          · exact selectionSetLookupValid_pruneKnownFalseSelections schema
              variableValues parentType rest htail
          · unfold NormalForm.selectionSetLookupValid
            intro candidate hcandidate
            rcases List.mem_cons.mp hcandidate with rfl | hrest
            · cases typeCondition with
              | none =>
                  simpa [NormalForm.selectionLookupValid] using
                    selectionSetLookupValid_pruneKnownFalseSelections schema
                      variableValues parentType childSelectionSet
                      (by simpa [NormalForm.selectionLookupValid] using hhead)
              | some fragmentType =>
                  simpa [NormalForm.selectionLookupValid] using
                    selectionSetLookupValid_pruneKnownFalseSelections schema
                      variableValues fragmentType childSelectionSet
                      (by simpa [NormalForm.selectionLookupValid] using hhead)
            · have htailPruned :=
                selectionSetLookupValid_pruneKnownFalseSelections schema
                  variableValues parentType rest htail
              unfold NormalForm.selectionSetLookupValid at htailPruned
              exact htailPruned candidate hrest
termination_by selectionSet => SelectionSet.size selectionSet
decreasing_by
  all_goals
    simp_wf
    simp_all [SelectionSet.size, Selection.size]
    omega

theorem SelectionSetSourceValid.pruneKnownFalseSelections
    (schema : Schema) (variableDefinitions : List VariableDefinition)
    (variableValues : Execution.VariableValues) (parentType : Name)
    : ∀ selectionSet,
        SelectionSetSourceValid schema variableDefinitions parentType selectionSet
        -> SelectionSetSourceValid schema variableDefinitions parentType
            (pruneKnownFalseSelections variableValues selectionSet)
  | [], _hvalid => by
      simp [GraphQL.ConditionTree.pruneKnownFalseSelections,
        SelectionSetSourceValid]
  | selection :: rest, hvalid => by
      unfold SelectionSetSourceValid at hvalid
      have hhead := hvalid selection (by simp)
      have htail : SelectionSetSourceValid schema variableDefinitions parentType rest := by
        unfold SelectionSetSourceValid
        intro candidate hcandidate
        exact hvalid candidate (by simp [hcandidate])
      cases selection with
      | field responseName fieldName arguments directives childSelectionSet =>
          unfold GraphQL.ConditionTree.pruneKnownFalseSelections
          split
          · exact SelectionSetSourceValid.pruneKnownFalseSelections schema
              variableDefinitions variableValues parentType rest htail
          · unfold SelectionSetSourceValid
            intro candidate hcandidate
            rcases List.mem_cons.mp hcandidate with rfl | hrest
            · simpa only [SelectionSourceValid] using hhead
            · have hpruned :=
                SelectionSetSourceValid.pruneKnownFalseSelections schema
                  variableDefinitions variableValues parentType rest htail
              unfold SelectionSetSourceValid at hpruned
              exact hpruned candidate hrest
      | inlineFragment typeCondition directives childSelectionSet =>
          unfold GraphQL.ConditionTree.pruneKnownFalseSelections
          split
          · exact SelectionSetSourceValid.pruneKnownFalseSelections schema
              variableDefinitions variableValues parentType rest htail
          · unfold SelectionSetSourceValid
            intro candidate hcandidate
            rcases List.mem_cons.mp hcandidate with rfl | hrest
            · cases typeCondition with
              | none =>
                  simp only [SelectionSourceValid] at hhead ⊢
                  exact SelectionSetSourceValid.pruneKnownFalseSelections schema
                    variableDefinitions variableValues parentType childSelectionSet hhead
              | some fragmentType =>
                  simp only [SelectionSourceValid] at hhead ⊢
                  exact SelectionSetSourceValid.pruneKnownFalseSelections schema
                    variableDefinitions variableValues fragmentType childSelectionSet
                    hhead
            · have hpruned :=
                SelectionSetSourceValid.pruneKnownFalseSelections schema
                  variableDefinitions variableValues parentType rest htail
              unfold SelectionSetSourceValid at hpruned
              exact hpruned candidate hrest
termination_by selectionSet => SelectionSet.size selectionSet
decreasing_by
  all_goals
    simp_wf
    simp_all [SelectionSet.size, Selection.size]
    omega

/-- Extraction from a source-valid selection set retains validation witnesses on every
stored field occurrence. -/
theorem ofSelectionSetInScope_fieldsValid
    (schema : Schema) (variableDefinitions : List VariableDefinition)
    (parentType : Name) (inherited : List BooleanLiteral)
    (selectionSet : List Selection)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (hvalid : SelectionSetSourceValid schema variableDefinitions parentType selectionSet)
    : TreeFieldsValid schema variableDefinitions
        (ConditionTree.ofSelectionSetInScope schema parentType inherited
          selectionSet) := by
  intro entry hentry
  rw [ofSelectionSetInScope_fieldEntries_mem schema parentType inherited selectionSet]
    at hentry
  apply collectConditionEntries_fieldsValid schema variableDefinitions parentType
    inherited (rootCondition schema parentType) selectionSet hschema
  · intro selection hselection
    unfold SelectionSetSourceValid at hvalid
    exact ⟨parentType, hvalid selection hselection,
      by intro runtimeType hruntime; exact hruntime⟩
  · exact hentry

/-- Known-false pruning preserves the source validation witnesses used by condition-tree
extraction. -/
theorem ofSelectionSetInScopeWithKnownFalsePruning_fieldsValid
    (schema : Schema) (variableDefinitions : List VariableDefinition)
    (parentType : Name) (inherited : List BooleanLiteral)
    (variableValues : Execution.VariableValues) (selectionSet : List Selection)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (hvalid : SelectionSetSourceValid schema variableDefinitions parentType selectionSet)
    : TreeFieldsValid schema variableDefinitions
        (ConditionTree.ofSelectionSetInScopeWithKnownFalsePruning schema parentType
          inherited variableValues selectionSet) := by
  unfold ConditionTree.ofSelectionSetInScopeWithKnownFalsePruning
  exact ofSelectionSetInScope_fieldsValid schema variableDefinitions parentType
    inherited _ hschema
      (SelectionSetSourceValid.pruneKnownFalseSelections schema variableDefinitions
        variableValues parentType selectionSet hvalid)

theorem SelectionsValidForCondition.pruneKnownFalseSelections
    (schema : Schema) (variableDefinitions : List VariableDefinition)
    (variableValues : Execution.VariableValues) (condition : Condition)
    : ∀ selectionSet,
        SelectionsValidForCondition schema variableDefinitions condition selectionSet
        -> SelectionsValidForCondition schema variableDefinitions condition
            (ConditionTree.pruneKnownFalseSelections variableValues selectionSet)
  | [], _hvalid => by
      simp [GraphQL.ConditionTree.pruneKnownFalseSelections,
        SelectionsValidForCondition]
  | selection :: rest, hvalid => by
      have hhead := hvalid selection (by simp)
      have htail : SelectionsValidForCondition schema variableDefinitions condition
          rest := by
        intro candidate hcandidate
        exact hvalid candidate (by simp [hcandidate])
      cases selection with
      | field responseName fieldName arguments directives childSelectionSet =>
          unfold GraphQL.ConditionTree.pruneKnownFalseSelections
          split
          · exact SelectionsValidForCondition.pruneKnownFalseSelections schema
              variableDefinitions variableValues condition rest htail
          · intro candidate hcandidate
            rcases List.mem_cons.mp hcandidate with rfl | hrest
            · exact hhead
            · have hpruned :=
                SelectionsValidForCondition.pruneKnownFalseSelections schema
                  variableDefinitions variableValues condition rest htail
              exact hpruned candidate hrest
      | inlineFragment typeCondition directives childSelectionSet =>
          unfold GraphQL.ConditionTree.pruneKnownFalseSelections
          split
          · exact SelectionsValidForCondition.pruneKnownFalseSelections schema
              variableDefinitions variableValues condition rest htail
          · intro candidate hcandidate
            rcases List.mem_cons.mp hcandidate with rfl | hrest
            · rcases hhead with ⟨validationParent, hsource, hscope⟩
              refine ⟨validationParent, ?_, hscope⟩
              cases typeCondition with
              | none =>
                  simp only [SelectionSourceValid] at hsource ⊢
                  exact SelectionSetSourceValid.pruneKnownFalseSelections schema
                    variableDefinitions variableValues validationParent
                    childSelectionSet hsource
              | some fragmentType =>
                  simp only [SelectionSourceValid] at hsource ⊢
                  exact SelectionSetSourceValid.pruneKnownFalseSelections schema
                    variableDefinitions variableValues fragmentType childSelectionSet
                    hsource
            · have hpruned :=
                SelectionsValidForCondition.pruneKnownFalseSelections schema
                  variableDefinitions variableValues condition rest htail
              exact hpruned candidate hrest
termination_by selectionSet => SelectionSet.size selectionSet
decreasing_by
  all_goals
    simp_wf
    simp_all [SelectionSet.size, Selection.size]
    omega

/-- The merged children of a validated group may be checked under the output type of
any concrete implementation active for that group. Each occurrence keeps its own
source definition only in this proof. -/
theorem CollectedFieldGroup.mergedSelectionSet_validForImplementation
    (schema : Schema) (variableDefinitions : List VariableDefinition)
    (group : CollectedFieldGroup) (runtimeParent : Name)
    (definition : FieldDefinition)
    (hvalid : group.FieldsValid schema variableDefinitions)
    (hparent : runtimeParent ∈ group.condition.possibleTypes)
    (hfieldNames
      : ∀ field,
          field ∈ group.fields -> field.fieldName = group.representativeField.fieldName)
    (hlookup
      : schema.lookupField runtimeParent group.representativeField.fieldName
        = some definition)
    : SelectionsValidForCondition schema variableDefinitions
        (rootCondition schema definition.outputType.namedType)
        group.mergedSelectionSet := by
  intro selection hselection
  unfold CollectedFieldGroup.mergedSelectionSet
    ConditionTree.FieldGroup.mergedSelectionSet
    SelectionSet.mergeSelectionSets at hselection
  rcases List.mem_flatMap.mp hselection with
    ⟨outerSelection, houter, hchild⟩
  change outerSelection ∈ group.fieldGroup.fields.map
    (ConditionTree.Field.toSelection group.fieldGroup.responseName) at houter
  rcases List.mem_map.mp houter with ⟨outerField, houterField, heq⟩
  subst outerSelection
  have hentry := hvalid _ (List.mem_map.mpr ⟨outerField, houterField, rfl⟩)
  simp only [FieldEntryValid, ConditionTree.Field.toSelection] at hentry
  rcases hentry with ⟨expectedDefinition, hdefinitions, hchildren⟩
  rcases hdefinitions runtimeParent hparent with
    ⟨implementation, himplementation, hsubtype⟩
  have hfieldName := hfieldNames outerField houterField
  have himplementationEq : implementation = definition := by
    rw [hfieldName, hlookup] at himplementation
    exact Option.some.inj himplementation.symm
  subst implementation
  have hchild' : selection ∈ outerField.selectionSet := by
    simpa [ConditionTree.Field.toSelection, Selection.subselections] using hchild
  have hselectionValid : Validation.selectionValid schema variableDefinitions
      expectedDefinition.outputType.namedType selection := by
    simp only [Validation.fieldSelectionSetValid] at hchildren
    rcases hchildren with ⟨_houtput, hshape⟩
    rcases hshape with hleaf | hcomposite
    · rw [hleaf.2] at hchild'
      simp at hchild'
    · unfold Validation.selectionSetValid at hcomposite
      exact hcomposite.2.2 selection hchild'
  refine ⟨expectedDefinition.outputType.namedType,
    SelectionSourceValid.of_selectionValid hselectionValid, ?_⟩
  intro childRuntime hchildRuntime
  have hincludeImplementation : schema.typeIncludesObjectBool
      definition.outputType.namedType childRuntime = true := by
    exact List.contains_iff_mem.mpr hchildRuntime
  exact List.contains_iff_mem.mp
    (typeIncludesObjectBool_of_outputTypeSubtype_namedType schema hsubtype
      hincludeImplementation)

/-- Child extraction under one active implementation retains all field-definition
validity witnesses without storing a source parent in executable syntax. -/
theorem CollectedFieldGroup.childTreeWithKnownFalsePruning_fieldsValid
    (schema : Schema) (variableDefinitions : List VariableDefinition)
    (group : CollectedFieldGroup) (runtimeParent : Name)
    (definition : FieldDefinition) (variableValues : Execution.VariableValues)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (hvalid : group.FieldsValid schema variableDefinitions)
    (hparent : runtimeParent ∈ group.condition.possibleTypes)
    (hfieldNames
      : ∀ field,
          field ∈ group.fields -> field.fieldName = group.representativeField.fieldName)
    (hlookup
      : schema.lookupField runtimeParent group.representativeField.fieldName
        = some definition)
    : TreeFieldsValid schema variableDefinitions
        (group.childTreeWithKnownFalsePruning schema definition.outputType.namedType
          variableValues) := by
  unfold CollectedFieldGroup.childTreeWithKnownFalsePruning
  intro entry hentry
  unfold ConditionTree.ofSelectionSetInScopeWithKnownFalsePruning at hentry
  rw [ofSelectionSetInScope_fieldEntries_mem schema definition.outputType.namedType
    group.childInheritedBooleanCondition
    (ConditionTree.pruneKnownFalseSelections variableValues
      group.mergedSelectionSet)] at hentry
  exact collectConditionEntries_fieldsValid schema variableDefinitions
    definition.outputType.namedType group.childInheritedBooleanCondition
    (rootCondition schema definition.outputType.namedType)
    (ConditionTree.pruneKnownFalseSelections variableValues group.mergedSelectionSet)
    hschema
    (SelectionsValidForCondition.pruneKnownFalseSelections schema variableDefinitions
      variableValues (rootCondition schema definition.outputType.namedType)
      group.mergedSelectionSet
      (group.mergedSelectionSet_validForImplementation schema variableDefinitions
        runtimeParent definition hvalid hparent hfieldNames hlookup)) entry hentry

/-- Every stored source field in a condition tree extracted from lookup-valid syntax has
compatible possible runtime definitions. -/
theorem ofSelectionSetInScope_fieldEntries_definitionsCompatible
    (schema : Schema) (parentType : Name) (inherited : List BooleanLiteral)
    (selectionSet : List Selection)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (hlookup : NormalForm.selectionSetLookupValid schema parentType selectionSet)
    : ∀ entry,
        entry
          ∈ (ConditionTree.ofSelectionSetInScope schema parentType inherited
              selectionSet).fieldEntries
        -> FieldEntryDefinitionsCompatible schema entry := by
  intro entry hentry
  rw [ofSelectionSetInScope_fieldEntries_mem schema parentType inherited selectionSet]
    at hentry
  exact collectConditionEntries_definitionsCompatible schema parentType inherited
    (rootCondition schema parentType) selectionSet hschema hlookup
    (by intro runtimeType hruntime; exact hruntime) entry hentry

end TreeSummary
end GraphQL
